// use slope_types::{Gc, Interner, Pair, Parameters, Root, Trace, Value, Vector};

// #[derive(Root, Default, Trace)]
// struct Strings<'gc> {
//     vec: Vec<Gc<'gc, String>>,
// }

// impl<'gc> Strings<'gc> {
//     fn push(&mut self, val: Gc<'gc, String>) {
//         self.vec.push(val);
//     }

//     fn pop(&mut self) -> Option<Gc<'gc, String>> {
//         self.vec.pop()
//     }
// }

// #[test]
// fn test_mutation() {
//     let _ = simple_logger::init();

//     let mut root = Strings::root(Parameters::zealous());

//     let mut ctx = root.mutate();
//     let val1 = ctx.alloc("foo".to_owned());
//     let val2 = ctx.alloc("bar".to_owned());
//     let _ = ctx.alloc("baz".to_owned());
//     let _ = ctx.alloc("qux".to_owned());
//     ctx.root.push(val1);
//     ctx.root.push(val2);
//     drop(ctx);

//     // Remove from root before allocating. Collection should be delayed until
//     // context is dropped, or val1/val2 will be permaturely deallocated.
//     let mut ctx = root.mutate();
//     let val2 = ctx.root.pop().unwrap();
//     let val1 = ctx.root.pop().unwrap();
//     assert_eq!(ctx.alloc("foo".to_owned()), val1);
//     assert_eq!(ctx.alloc("bar".to_owned()), val2);
// }

// #[test]
// fn test_pair_and_list() {
//     let _ = simple_logger::init();

//     let mut root = Strings::root(Parameters::zealous());

//     let mut interner = Interner::default();
//     let mut ctx = root.mutate();
//     let val1 = interner.intern("foo");
//     let val2 = interner.intern("bar");
//     let val3 = interner.intern("baz");
//     let pair1 = ctx.alloc(Pair::new(val2, val3));
//     let pair2 = ctx.alloc(Pair::new(val1, pair1));
//     let string = Value::from(pair2).display(&interner).to_string();
//     assert_eq!("(foo bar . baz)", string);

//     let list = ctx.alloc_list([val1, val2, val3].iter().map(Value::from));
//     let string = list.display(&interner).to_string();
//     assert_eq!("(foo bar baz)", string);
// }

// #[test]
// fn test_vector() {
//     let _ = simple_logger::init();

//     let mut root = Strings::root(Parameters::zealous());

//     let mut interner = Interner::default();
//     let mut ctx = root.mutate();
//     let val1 = interner.intern("foo");
//     let val2 = interner.intern("bar");
//     let val3 = interner.intern("baz");
//     let vector = ctx.alloc(Vector::new([val1, val2, val3].iter().map(Value::from)));
//     let string = Value::from(vector).display(&interner).to_string();
//     assert_eq!("[foo bar baz]", string);
// }

// #[test]
// fn test_dangling() {
//     let _ = simple_logger::init();

//     let mut root = Strings::root(Parameters::zealous());

//     let mut ctx = root.mutate();
//     ctx.root.push(unsafe { Gc::dangling() });
//     ctx.root.push(unsafe { Gc::dangling() });
//     let val1 = ctx.alloc("foo".to_owned());
//     ctx.root.push(val1);
//     drop(ctx);

//     let mut ctx = root.mutate();
//     let val1 = ctx.alloc("foo".to_owned());
//     assert_eq!(ctx.root.pop().unwrap(), val1);
// }
