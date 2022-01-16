#[macro_export]
macro_rules! static_assert {
    ($test:expr) => {
        #[allow(dead_code)]
        const _: () = [()][!($test as bool) as usize];
    };
}

#[macro_export]
macro_rules! static_assert_size {
    ($ty:ty, $size:expr) => {
        #[allow(dead_code)]
        const _: [(); $size] = [(); ::std::mem::size_of::<$ty>()];
    };
}

#[macro_export]
macro_rules! repeat_pattern {
    ($exp:expr) => {
        $crate::syntax::Pattern::Repeat(Box::new($exp.into()))
    };
}

#[macro_export]
macro_rules! list_pattern {
    ($($exp:expr, )+) => {
        $crate::syntax::ListPattern {
            patterns: Box::new([
                $($exp.into(),)+
            ])
        }
    };
}
