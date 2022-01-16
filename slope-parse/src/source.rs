use std::{
    fmt, fmt::Debug, fmt::Display, fmt::Formatter, ops::Add, ops::Range, ops::Sub, path::PathBuf,
};

#[derive(Debug)]
pub enum FileName {
    Named(PathBuf),
    Virtual(String),
}

#[derive(Debug)]
pub struct SourceFile {
    name: FileName,
    lines: Vec<BytePos>,
}

// This needs to be small, because we use it a lot.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BytePos(u32);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CharPos(u32);

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ByteRange {
    pub hi: BytePos,
    pub lo: BytePos,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct PosInfo {
    pub line: u32,
    pub column: CharPos,
}

impl SourceFile {
    pub fn new(name: FileName, offset: BytePos, source: &str) -> Self {
        let mut lines = vec![offset];

        for (pos, chr) in source.char_indices() {
            if chr == '\n' {
                lines.push(BytePos(pos as u32 + 1));
            }
        }

        Self { name, lines }
    }

    pub fn lookup_pos_info(&self, offset: BytePos) -> Option<PosInfo> {
        let line = self.lookup_line(offset)?;
        let column = CharPos(offset.0 - self.lines[line as usize].0);

        Some(PosInfo { line, column })
    }

    pub fn lookup_line(&self, offset: BytePos) -> Option<u32> {
        match self.lines.binary_search(&offset) {
            Ok(line) => Some(line as u32),
            Err(line) => (line as u32).checked_sub(1),
        }
    }
}

impl BytePos {
    #[inline]
    pub fn is_undefined(&self) -> bool {
        self.0 == u32::MAX
    }
}

impl From<i32> for BytePos {
    #[inline]
    fn from(val: i32) -> Self {
        Self(val as u32)
    }
}

impl From<u32> for BytePos {
    #[inline]
    fn from(val: u32) -> Self {
        Self(val)
    }
}

impl From<usize> for BytePos {
    #[inline]
    fn from(val: usize) -> Self {
        Self(val as u32)
    }
}

impl<T: Into<BytePos>> From<Range<T>> for ByteRange {
    #[inline]
    fn from(val: Range<T>) -> Self {
        Self {
            lo: val.start.into(),
            hi: val.end.into(),
        }
    }
}

impl Display for BytePos {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        if self.0 == u32::MAX {
            write!(fmt, "(unknown)")
        } else {
            write!(fmt, "{}", self.0)
        }
    }
}

impl Display for CharPos {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}", self.0)
    }
}

impl Debug for BytePos {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self, fmt)
    }
}

impl Debug for CharPos {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self, fmt)
    }
}

impl Display for ByteRange {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        if self.lo.0 == u32::MAX || self.hi.0 == u32::MAX {
            write!(fmt, "(unknown)")
        } else {
            write!(fmt, "{}..{}", self.lo, self.hi)
        }
    }
}

impl Debug for ByteRange {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self, fmt)
    }
}

impl Default for BytePos {
    fn default() -> Self {
        // Sentinel value for NONE.
        // Using an option type requires another bit free in the Node struct.
        BytePos(u32::MAX)
    }
}

impl Add<u32> for BytePos {
    type Output = BytePos;

    #[inline]
    fn add(self, rhs: u32) -> Self::Output {
        BytePos(self.0 + rhs)
    }
}

impl Sub<u32> for BytePos {
    type Output = BytePos;

    #[inline]
    fn sub(self, rhs: u32) -> Self::Output {
        BytePos(self.0 - rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lookup_line() {
        let source = SourceFile {
            name: FileName::Virtual("test".to_owned()),
            lines: vec![1.into(), 5.into(), 9.into()],
        };

        assert_eq!(Some(1), source.lookup_line(BytePos(5)));
        assert_eq!(Some(1), source.lookup_line(BytePos(7)));
    }

    #[test]
    fn test_lookup_line_if_lines_are_empty() {
        let source = SourceFile {
            name: FileName::Virtual("test".to_owned()),
            lines: vec![],
        };

        assert_eq!(None, source.lookup_line(BytePos(1)));
    }

    #[test]
    fn test_lookup_pos_info() {
        let source = SourceFile {
            name: FileName::Virtual("test".to_owned()),
            lines: vec![1.into(), 5.into(), 9.into()],
        };

        assert_eq!(
            Some(PosInfo {
                line: 1,
                column: CharPos(0),
            }),
            source.lookup_pos_info(BytePos(5))
        );

        assert_eq!(
            Some(PosInfo {
                line: 1,
                column: CharPos(2),
            }),
            source.lookup_pos_info(BytePos(7))
        );
    }

    #[test]
    fn test_lookup_pos_info_if_lines_are_empty() {
        let source = SourceFile {
            name: FileName::Virtual("test".to_owned()),
            lines: vec![],
        };

        assert_eq!(None, source.lookup_pos_info(BytePos(1)));
    }
}
