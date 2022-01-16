use memchr::memchr;
use rustyline::highlight::Highlighter;
use std::{
    borrow::Cow::{self, Borrowed, Owned},
    cell::Cell,
};

const ALL: &[u8; 6] = b"(){}[]";
const OPENS: &[u8; 3] = b"({[";
const CLOSES: &[u8; 3] = b")}]";

/// Highlight matching bracket when typed or cursor moved on.
#[derive(Default)]
pub struct MatchingBracketHighlighter {
    bracket: Cell<Option<(u8, usize)>>, // memorize the character to search...
}

impl Highlighter for MatchingBracketHighlighter {
    fn highlight<'l>(&self, line: &'l str, _pos: usize) -> Cow<'l, str> {
        if line.is_empty() {
            return Borrowed(line);
        }

        // Highlight matching brace/bracket/parenthesis if it exists
        if let Some((bracket, pos)) = self.bracket.get() {
            if let Some((matching, idx)) = find_matching_bracket(line, pos, bracket) {
                let mut copy = line.to_owned();
                if idx > pos {
                    copy.replace_range(
                        idx..=idx,
                        &format!("\x1b[1;96m{}\x1b[0m", matching as char),
                    );
                    copy.replace_range(pos..=pos, &format!("\x1b[1;96m{}\x1b[0m", bracket as char));
                } else {
                    copy.replace_range(pos..=pos, &format!("\x1b[1;96m{}\x1b[0m", bracket as char));
                    copy.replace_range(
                        idx..=idx,
                        &format!("\x1b[1;96m{}\x1b[0m", matching as char),
                    );
                }
                return Owned(copy);
            } else if is_close_bracket(bracket) {
                let mut copy = line.to_owned();
                copy.replace_range(pos..=pos, &format!("\x1b[1;91m{}\x1b[0m", bracket as char));
                return Owned(copy);
            }
        }

        Borrowed(line)
    }

    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.bracket.set(check_bracket(line, pos));
        self.bracket.get().is_some()
    }
}

fn find_matching_bracket(line: &str, pos: usize, bracket: u8) -> Option<(u8, usize)> {
    let matching = matching_bracket(bracket);
    let mut idx;
    let mut unmatched = 1;
    if is_open_bracket(bracket) {
        // forward search
        idx = pos + 1;
        let bytes = &line.as_bytes()[idx..];
        for b in bytes {
            if *b == matching {
                unmatched -= 1;
                if unmatched == 0 {
                    debug_assert_eq!(matching, line.as_bytes()[idx]);
                    return Some((matching, idx));
                }
            } else if *b == bracket {
                unmatched += 1;
            }
            idx += 1;
        }
        debug_assert_eq!(idx, line.len());
    } else {
        // backward search
        idx = pos;
        let bytes = &line.as_bytes()[..idx];
        for b in bytes.iter().rev() {
            if *b == matching {
                unmatched -= 1;
                if unmatched == 0 {
                    debug_assert_eq!(matching, line.as_bytes()[idx - 1]);
                    return Some((matching, idx - 1));
                }
            } else if *b == bracket {
                unmatched += 1;
            }
            idx -= 1;
        }
        debug_assert_eq!(idx, 0);
    }
    None
}

// check under or before the cursor
fn check_bracket(line: &str, pos: usize) -> Option<(u8, usize)> {
    if line.is_empty() {
        return None;
    }

    let mut pos = pos;
    if pos >= line.len() {
        pos = line.len() - 1; // before cursor
        let b = line.as_bytes()[pos]; // previous byte
        if is_bracket(b) {
            Some((b, pos))
        } else {
            None
        }
    } else {
        let mut under_cursor = true;
        loop {
            let b = line.as_bytes()[pos];
            if is_bracket(b) {
                return Some((b, pos));
            } else if under_cursor && pos > 0 {
                under_cursor = false;
                pos -= 1; // or before cursor
            } else {
                return None;
            }
        }
    }
}

fn matching_bracket(bracket: u8) -> u8 {
    match bracket {
        b'(' => b')',
        b')' => b'(',
        b => b,
    }
}

fn is_bracket(bracket: u8) -> bool {
    memchr(bracket, ALL).is_some()
}

fn is_open_bracket(bracket: u8) -> bool {
    memchr(bracket, OPENS).is_some()
}

fn is_close_bracket(bracket: u8) -> bool {
    memchr(bracket, CLOSES).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn test_find_matching_bracket() {
        assert_eq!(find_matching_bracket("(...", 0, b'('), None);
        assert_eq!(find_matching_bracket("...)", 3, b')'), None);

        assert_eq!(find_matching_bracket("()..", 0, b'('), Some((b')', 1)));
        assert_eq!(find_matching_bracket("(..)", 0, b'('), Some((b')', 3)));

        assert_eq!(find_matching_bracket("..()", 3, b')'), Some((b'(', 2)));
        assert_eq!(find_matching_bracket("(..)", 3, b')'), Some((b'(', 0)));

        assert_eq!(find_matching_bracket("(())", 0, b'('), Some((b')', 3)));
        assert_eq!(find_matching_bracket("(())", 3, b')'), Some((b'(', 0)));
    }

    #[test]
    pub fn test_check_bracket() {
        assert_eq!(check_bracket("", 0), None);

        assert_eq!(check_bracket(")...", 0), Some((b')', 0)));
        assert_eq!(check_bracket("(...", 2), None);
        assert_eq!(check_bracket("...(", 3), Some((b'(', 3)));
        assert_eq!(check_bracket("...(", 4), Some((b'(', 3)));
        assert_eq!(check_bracket("..).", 4), None);

        assert_eq!(check_bracket("(...", 0), Some((b'(', 0)));
        assert_eq!(check_bracket("(...", 1), Some((b'(', 0)));
        assert_eq!(check_bracket("...)", 3), Some((b')', 3)));
        assert_eq!(check_bracket("...)", 4), Some((b')', 3)));
    }

    #[test]
    pub fn test_matching_bracket() {
        assert_eq!(matching_bracket(b'('), b')');
        assert_eq!(matching_bracket(b')'), b'(');
    }

    #[test]
    pub fn test_is_open_bracket() {
        assert!(is_open_bracket(b'('));
        assert!(is_close_bracket(b')'));
    }
}
