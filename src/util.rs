//! Small dependency-free helpers: duration parsing, formatting, a deterministic
//! PRNG, a bitset, and best-effort RSS reporting.

use anyhow::{bail, Result};
use std::time::Duration;

// ---------------------------------------------------------------------------
// Duration parsing / formatting
// ---------------------------------------------------------------------------

/// Parse `30s`, `45m`, `12h`, `7d`, `500ms`, or a bare integer (seconds).
pub fn parse_duration(s: &str) -> Result<Duration> {
    let s = s.trim();
    if s.is_empty() {
        bail!("empty duration");
    }
    let (num, unit) = split_numeric(s);
    if num.is_empty() {
        bail!("duration `{s}` has no numeric part");
    }
    let v: u64 = num
        .parse()
        .map_err(|_| anyhow::anyhow!("duration `{s}`: `{num}` is not an integer"))?;
    let d = match unit {
        "" | "s" | "sec" | "secs" => Duration::from_secs(v),
        "ms" => Duration::from_millis(v),
        "m" | "min" | "mins" => Duration::from_secs(v * 60),
        "h" | "hr" | "hrs" => Duration::from_secs(v * 3600),
        "d" | "day" | "days" => Duration::from_secs(v * 86400),
        other => bail!("duration `{s}`: unknown unit `{other}` (use ms, s, m, h, d)"),
    };
    Ok(d)
}

/// Parse a byte size: `8GiB`, `512MiB`, `1000000`, `4GB`.
pub fn parse_bytes(s: &str) -> Result<u64> {
    let s = s.trim();
    let (num, unit) = split_numeric(s);
    if num.is_empty() {
        bail!("byte size `{s}` has no numeric part");
    }
    let v: u64 = num
        .parse()
        .map_err(|_| anyhow::anyhow!("byte size `{s}`: `{num}` is not an integer"))?;
    let mult = match unit.to_ascii_lowercase().as_str() {
        "" | "b" => 1u64,
        "k" | "kb" | "kib" => 1 << 10,
        "m" | "mb" | "mib" => 1 << 20,
        "g" | "gb" | "gib" => 1 << 30,
        "t" | "tb" | "tib" => 1u64 << 40,
        other => bail!("byte size `{s}`: unknown unit `{other}`"),
    };
    Ok(v * mult)
}

fn split_numeric(s: &str) -> (&str, &str) {
    let idx = s
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(s.len());
    (&s[..idx], s[idx..].trim())
}

/// `2:14:07` style elapsed formatting (hours are not zero padded).
pub fn fmt_hms(d: Duration) -> String {
    let total = d.as_secs();
    format!("{}:{:02}:{:02}", total / 3600, (total / 60) % 60, total % 60)
}

/// Thousands separators.
pub fn commas(n: u64) -> String {
    let s = n.to_string();
    let mut out = String::with_capacity(s.len() + s.len() / 3);
    let bytes = s.as_bytes();
    for (i, b) in bytes.iter().enumerate() {
        if i > 0 && (bytes.len() - i) % 3 == 0 {
            out.push(',');
        }
        out.push(*b as char);
    }
    out
}

pub fn fmt_bytes(b: u64) -> String {
    const UNITS: [&str; 5] = ["B", "KiB", "MiB", "GiB", "TiB"];
    let mut v = b as f64;
    let mut u = 0;
    while v >= 1024.0 && u + 1 < UNITS.len() {
        v /= 1024.0;
        u += 1;
    }
    if u == 0 {
        format!("{} B", b)
    } else {
        format!("{:.1} {}", v, UNITS[u])
    }
}

/// Compact scientific-ish rendering used by the human stats display.
pub fn fmt_sci(v: f64) -> String {
    if v == 0.0 {
        return "0".to_string();
    }
    if v.abs() < 1e5 {
        return commas(v as u64);
    }
    format!("{:.2e}", v)
}

/// `12.4k`, `2.1M`, `840` — for rate columns.
pub fn fmt_rate(v: f64) -> String {
    if v >= 1e9 {
        format!("{:.1}G", v / 1e9)
    } else if v >= 1e6 {
        format!("{:.1}M", v / 1e6)
    } else if v >= 1e3 {
        format!("{:.1}k", v / 1e3)
    } else {
        format!("{:.0}", v)
    }
}

// ---------------------------------------------------------------------------
// Deterministic PRNG (splitmix64)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct Rng {
    state: u64,
}

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng {
            state: seed.wrapping_add(0x9E37_79B9_7F4A_7C15),
        }
    }
    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    /// Uniform in `[0, bound)` (bound > 0). Rejection-free Lemire-style reduction;
    /// the tiny modulo bias is irrelevant for sampling links.
    pub fn below(&mut self, bound: u64) -> u64 {
        ((self.next_u64() as u128 * bound as u128) >> 64) as u64
    }
    pub fn state(&self) -> u64 {
        self.state
    }
    pub fn from_state(state: u64) -> Self {
        Rng { state }
    }
}

// ---------------------------------------------------------------------------
// Bitset
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct Bitset {
    words: Vec<u64>,
}

impl Bitset {
    pub fn new(n: usize) -> Self {
        Bitset {
            words: vec![0u64; n.div_ceil(64)],
        }
    }
    #[inline]
    pub fn clear(&mut self, i: usize) {
        self.words[i >> 6] &= !(1u64 << (i & 63));
    }
    /// Set and report whether it was previously unset.
    #[inline]
    pub fn test_and_set(&mut self, i: usize) -> bool {
        let w = &mut self.words[i >> 6];
        let b = 1u64 << (i & 63);
        let was = *w & b == 0;
        *w |= b;
        was
    }
    pub fn bytes(&self) -> u64 {
        (self.words.len() * 8) as u64
    }
}

// ---------------------------------------------------------------------------
// Resident set size
// ---------------------------------------------------------------------------

/// Current RSS in bytes. Linux only (reads `/proc/self/statm`); returns `None`
/// elsewhere, where the caller falls back to the engine's own accounting.
pub fn rss_bytes() -> Option<u64> {
    #[cfg(target_os = "linux")]
    {
        let s = std::fs::read_to_string("/proc/self/statm").ok()?;
        let pages: u64 = s.split_whitespace().nth(1)?.parse().ok()?;
        Some(pages * 4096)
    }
    #[cfg(not(target_os = "linux"))]
    {
        None
    }
}

/// CPU time consumed by this process, best effort.
pub fn cpu_time() -> Option<Duration> {
    #[cfg(target_os = "linux")]
    {
        let s = std::fs::read_to_string("/proc/self/stat").ok()?;
        // utime and stime are fields 14 and 15 (1-based) after the comm field.
        let close = s.rfind(')')?;
        let rest: Vec<&str> = s[close + 2..].split_whitespace().collect();
        let utime: u64 = rest.get(11)?.parse().ok()?;
        let stime: u64 = rest.get(12)?.parse().ok()?;
        Some(Duration::from_secs_f64((utime + stime) as f64 / 100.0))
    }
    #[cfg(not(target_os = "linux"))]
    {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn durations() {
        assert_eq!(parse_duration("30s").unwrap(), Duration::from_secs(30));
        assert_eq!(parse_duration("45m").unwrap(), Duration::from_secs(2700));
        assert_eq!(parse_duration("12h").unwrap(), Duration::from_secs(43200));
        assert_eq!(parse_duration("7d").unwrap(), Duration::from_secs(604800));
        assert_eq!(parse_duration("500ms").unwrap(), Duration::from_millis(500));
        assert!(parse_duration("banana").is_err());
    }

    #[test]
    fn byte_sizes() {
        assert_eq!(parse_bytes("8GiB").unwrap(), 8 << 30);
        assert_eq!(parse_bytes("512MiB").unwrap(), 512 << 20);
        assert_eq!(parse_bytes("1024").unwrap(), 1024);
    }

    #[test]
    fn formatting() {
        assert_eq!(commas(300540195), "300,540,195");
        assert_eq!(commas(0), "0");
        assert_eq!(commas(999), "999");
        assert_eq!(fmt_hms(Duration::from_secs(8047)), "2:14:07");
    }

    #[test]
    fn rng_is_deterministic() {
        let mut a = Rng::new(0);
        let mut b = Rng::new(0);
        for _ in 0..100 {
            assert_eq!(a.next_u64(), b.next_u64());
        }
    }
}
