//! Witness file format.
//!
//! This module is pure I/O: it does no combinatorics and makes no claim about
//! whether a witness is valid. Both the solver and the independent checker use
//! it, which does not violate the "no shared code" rule of spec section 6 —
//! the checker recomputes every mathematical property from the definitions.
//!
//! ```text
//! odd835-witness 1
//! kind partition          # or `code`
//! k 6
//! n 11
//! vertices 462
//! colors 7                # partition only
//! m 66
//! data
//! <payload>
//! ```
//!
//! For `partition` the payload is one base-36 digit per vertex in colex-rank
//! order, wrapped at 72 columns (colours 0..=16 fit in `0`..`g`).
//! For `code` the payload is the ascending decimal vertex indices, one per line.

use anyhow::{bail, Context, Result};
use std::fmt::Write as _;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::Path;

const MAGIC: &str = "odd835-witness";
const VERSION: u32 = 1;
const WRAP: usize = 72;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Witness {
    /// `color[v]` for every vertex `v` in colex order.
    Partition { k: u32, colors: Vec<u8> },
    /// Ascending vertex indices of a single perfect 1-code.
    Code { k: u32, members: Vec<u32> },
}

impl Witness {
    pub fn k(&self) -> u32 {
        match self {
            Witness::Partition { k, .. } | Witness::Code { k, .. } => *k,
        }
    }

    pub fn write(&self, path: &Path) -> Result<()> {
        let f = File::create(path).with_context(|| format!("creating {}", path.display()))?;
        let mut w = BufWriter::new(f);
        match self {
            Witness::Partition { k, colors } => {
                let n = 2 * k - 1;
                writeln!(w, "{MAGIC} {VERSION}")?;
                writeln!(w, "kind partition")?;
                writeln!(w, "k {k}")?;
                writeln!(w, "n {n}")?;
                writeln!(w, "vertices {}", colors.len())?;
                writeln!(w, "colors {}", k + 1)?;
                writeln!(w, "m {}", colors.len() as u64 / (*k as u64 + 1))?;
                writeln!(w, "data")?;
                let mut line = String::with_capacity(WRAP + 1);
                for (i, c) in colors.iter().enumerate() {
                    line.push(digit_to_char(*c)?);
                    if (i + 1) % WRAP == 0 {
                        writeln!(w, "{line}")?;
                        line.clear();
                    }
                }
                if !line.is_empty() {
                    writeln!(w, "{line}")?;
                }
            }
            Witness::Code { k, members } => {
                let n = 2 * k - 1;
                writeln!(w, "{MAGIC} {VERSION}")?;
                writeln!(w, "kind code")?;
                writeln!(w, "k {k}")?;
                writeln!(w, "n {n}")?;
                writeln!(w, "vertices {}", num_vertices(*k))?;
                writeln!(w, "m {}", members.len())?;
                writeln!(w, "data")?;
                let mut buf = String::new();
                for v in members {
                    buf.clear();
                    let _ = writeln!(buf, "{v}");
                    w.write_all(buf.as_bytes())?;
                }
            }
        }
        w.flush()?;
        Ok(())
    }

    pub fn read(path: &Path) -> Result<Witness> {
        let f = File::open(path).with_context(|| format!("opening {}", path.display()))?;
        let mut rd = BufReader::new(f);
        let mut line = String::new();

        rd.read_line(&mut line)?;
        let hdr: Vec<&str> = line.split_whitespace().collect();
        if hdr.len() != 2 || hdr[0] != MAGIC {
            bail!("{}: not an odd835 witness file", path.display());
        }
        let ver: u32 = hdr[1].parse().context("witness version")?;
        if ver != VERSION {
            bail!("witness version {ver} is not supported (expected {VERSION})");
        }

        let mut kind = String::new();
        let mut k = 0u32;
        let mut declared_vertices = 0u64;
        let mut declared_colors: Option<u32> = None;
        let mut declared_m: Option<u64> = None;

        loop {
            line.clear();
            if rd.read_line(&mut line)? == 0 {
                bail!("witness ended before the `data` marker");
            }
            let t = line.trim();
            if t == "data" {
                break;
            }
            let mut it = t.split_whitespace();
            let key = it.next().unwrap_or("");
            let val = it.next().unwrap_or("");
            match key {
                "kind" => kind = val.to_string(),
                "k" => k = val.parse().context("header k")?,
                "n" => { /* redundant, validated below */ }
                "vertices" => declared_vertices = val.parse().context("header vertices")?,
                "colors" => declared_colors = Some(val.parse().context("header colors")?),
                "m" => declared_m = Some(val.parse().context("header m")?),
                "" => {}
                other => bail!("unknown witness header key `{other}`"),
            }
        }

        if k < 2 || k > 16 {
            bail!("witness declares k = {k}, outside 2..=16");
        }
        let expect_v = num_vertices(k);
        if declared_vertices != expect_v {
            bail!(
                "witness declares {declared_vertices} vertices but k = {k} has {expect_v}"
            );
        }

        match kind.as_str() {
            "partition" => {
                if declared_colors != Some(k + 1) {
                    bail!(
                        "witness declares {:?} colours; a partition of O_{k} must use exactly {}",
                        declared_colors,
                        k + 1
                    );
                }
                let mut colors = Vec::with_capacity(expect_v as usize);
                for l in rd.lines() {
                    let l = l?;
                    for ch in l.trim().chars() {
                        colors.push(char_to_digit(ch)?);
                    }
                }
                if colors.len() as u64 != expect_v {
                    bail!(
                        "witness payload has {} entries, expected {expect_v}",
                        colors.len()
                    );
                }
                Ok(Witness::Partition { k, colors })
            }
            "code" => {
                let mut members = Vec::new();
                for l in rd.lines() {
                    let l = l?;
                    let t = l.trim();
                    if t.is_empty() {
                        continue;
                    }
                    members.push(t.parse::<u32>().with_context(|| format!("vertex index `{t}`"))?);
                }
                if let Some(m) = declared_m {
                    if members.len() as u64 != m {
                        bail!("witness declares m = {m} but lists {} members", members.len());
                    }
                }
                Ok(Witness::Code { k, members })
            }
            other => bail!("unknown witness kind `{other}`"),
        }
    }
}

fn num_vertices(k: u32) -> u64 {
    // C(2k-1, k-1), computed locally so the format module stays self-contained.
    let n = (2 * k - 1) as u64;
    let r = (k - 1) as u64;
    let mut v: u128 = 1;
    for i in 0..r {
        v = v * (n - i) as u128 / (i + 1) as u128;
    }
    v as u64
}

fn digit_to_char(c: u8) -> Result<char> {
    match c {
        0..=9 => Ok((b'0' + c) as char),
        10..=35 => Ok((b'a' + c - 10) as char),
        _ => bail!("colour {c} does not fit the base-36 witness encoding"),
    }
}

fn char_to_digit(ch: char) -> Result<u8> {
    match ch {
        '0'..='9' => Ok(ch as u8 - b'0'),
        'a'..='z' => Ok(ch as u8 - b'a' + 10),
        _ => bail!("invalid witness payload character `{ch}`"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vertex_count_agrees_with_binomials() {
        assert_eq!(num_vertices(2), 3);
        assert_eq!(num_vertices(4), 35);
        assert_eq!(num_vertices(6), 462);
        assert_eq!(num_vertices(16), 300_540_195);
    }

    #[test]
    fn partition_round_trip() {
        let dir = std::env::temp_dir().join("odd835-witness-test");
        std::fs::create_dir_all(&dir).unwrap();
        let p = dir.join("p.wit");
        let w = Witness::Partition {
            k: 4,
            colors: (0..35u32).map(|i| (i % 5) as u8).collect(),
        };
        w.write(&p).unwrap();
        assert_eq!(Witness::read(&p).unwrap(), w);
        let _ = std::fs::remove_file(&p);
    }

    #[test]
    fn code_round_trip() {
        let dir = std::env::temp_dir().join("odd835-witness-test");
        std::fs::create_dir_all(&dir).unwrap();
        let p = dir.join("c.wit");
        let w = Witness::Code {
            k: 4,
            members: vec![0, 3, 9, 17, 22, 30, 34],
        };
        w.write(&p).unwrap();
        assert_eq!(Witness::read(&p).unwrap(), w);
        let _ = std::fs::remove_file(&p);
    }
}
