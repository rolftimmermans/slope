use slope_parse::{AtomKind, SourceNode};
use std::{fmt::{self, Write}};

pub fn format(nodes: impl Iterator<Item = SourceNode>) -> String {
    let mut fmt = Formatter::default();
    fmt.fmt_top_nodes(nodes).expect("formatting failed");
    fmt.into_buf()
}

#[derive(Default)]
struct Formatter {
    buf: String,
    indent: usize,
}

fn all_trivial(nodes: &[&SourceNode]) -> bool {
    nodes.iter().all(|node| !node.is_list())
}

fn all_simple(nodes: &[&SourceNode]) -> bool {
    nodes.iter().all(|node| is_simple(node))
}

fn is_simple(node: &SourceNode) -> bool {
    match node {
        SourceNode::List { inner, .. } => inner.iter().all(|node| !node.is_list()),
        _ => true,
    }
}

fn nested_lists(mut node: &SourceNode) -> usize {
    let mut count = 0;

    while let SourceNode::List { inner, .. } = node {
        if let Some(first) = inner.first() {
            node = first;
            count += 1;
        }
    }

    count
}

impl Formatter {
    fn into_buf(self) -> String {
        self.buf
    }

    fn fmt_top_nodes(&mut self, nodes: impl Iterator<Item = SourceNode>) -> fmt::Result {
        let nodes = nodes.filter(|node| !node.is_whitespace()).collect::<Box<_>>();
        for node in nodes.iter() {
            self.fmt_node(node)?;
            write!(self.buf, "\n\n")?;
        }

        Ok(())
    }

    fn fmt_nodes<'s>(&mut self, nodes: impl Iterator<Item = &'s SourceNode>) -> fmt::Result {
        let nodes = nodes.filter(|node| !node.is_whitespace()).collect::<Box<_>>();
        // let total = nodes.len();
        // let is_all_trivial = all_trivial(nodes.as_ref());
        let is_all_simple = all_simple(nodes.as_ref());

        let mut nodes = nodes.iter();
        if let Some(node) = nodes.next() {
            // First item directly after opening parenthesis.
            self.fmt_node(node)?;

            if is_all_simple {
                // Inline everything if the list is simple enough.
                for node in nodes {
                    write!(self.buf, " ")?;
                    self.fmt_node(node)?;
                }
            } else {
                let mut nodes = nodes.peekable();
                if let Some(node) = nodes.peek() {
                    if is_simple(node) {
                        write!(self.buf, " ")?;
                        self.fmt_node(node)?;
                        nodes.next();
                    }

                    self.indent += 2;
                    for node in nodes {
                        write!(self.buf, "\n")?;
                        let indent = self.indent; // - nested_lists(node) + 1;
                        write!(self.buf, "{:indent$}", "", indent = indent)?;
                        self.fmt_node(node)?;
                    }
                    self.indent -= 2;
                }
            }
        }

        Ok(())
    }

    fn fmt_node(&mut self, node: &SourceNode) -> fmt::Result {
        match node {
            SourceNode::List { inner, .. } => {
                write!(self.buf, "(")?;
                self.fmt_nodes(inner.iter())?;
                write!(self.buf, ")")?;
            }

            SourceNode::Atom { kind: AtomKind::Whitespace, .. } => {}

            SourceNode::Atom { kind: AtomKind::String, atom, .. } => {
                write!(self.buf, "\"{atom}\"", atom = atom)?;
            }

            SourceNode::Atom { .. } => {
                write!(self.buf, "{node}", node = node)?;
            }

            SourceNode::Cons { inner, .. } => {
                write!(self.buf, ".")?;
                self.fmt_nodes(inner.iter())?;
            }

            SourceNode::Quoted { inner, .. } => {
                write!(self.buf, "'")?;
                self.fmt_node(inner)?;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use slope_parse::parse_lossless;
    use indoc::indoc;

    fn parse_fmt(src: &str) -> String {
        format(parse_lossless(src).map(Result::unwrap))
    }

    #[test]
    fn test_format_trivial() {
        let src = "(foo bar)";
        assert_eq!(parse_fmt(src), src);
    }

    #[test]
    fn test_form_let_form() {
        println!("{}", parse_fmt("(let ((a (+ 1 2 3)) (b (+ 1 2 3 4))) (+ a b))"));
        assert_eq!(
            parse_fmt("(let ((a (+ 1 2 3)) (b (+ 1 2 3 4))) (+ a b))"),
            indoc!("
                (let ((a (+ 1 2 3))
                      (b (+ 1 2 3 4)))
                  (+ a b))
            ")
        );
    }

    #[test]
    fn test_form_quicksort() {
        println!("{}", parse_fmt("(define (partition compare l1)
        (cond ;; lol match
           ((null? l1) '())
           ((compare (car l1)) (cons (car l1) (partition compare (cdr l1))))
           (else (partition compare (cdr l1)))))

     (define (quicksort l1)
        (cond
           ((null? l1) '())
           (else (let ((pivot (car l1)))
              (append (append (quicksort (partition (lambda (x) (< x pivot)) l1))
                         (partition (lambda (x) (= x pivot)) l1))
                      (quicksort (partition (lambda (x) (> x pivot)) l1)))))))
  "));
        assert_eq!(1, 2);
    }
}
