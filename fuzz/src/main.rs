use afl::*;
use slope_parse::parse_lossless;

fn main() {
    fuzz!(|data: &[u8]| {
        if let Ok(src) = std::str::from_utf8(data) {
            for expr in parse_lossless(src) {
                let _ = expr;
            }
        }
    });
}
