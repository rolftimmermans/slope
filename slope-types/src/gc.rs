pub use slope_derive::Root;

use std::{
    borrow::Borrow,
    cell::Cell,
    fmt::{Debug, Display, Formatter, Result},
    marker::PhantomData,
    mem::size_of,
    ops::Deref,
    ptr::NonNull,
};

use crate::{Closure, Function, Pair, Trace, Value, Vector};

pub trait Root: Default + Trace {
    type Rooted;

    fn root(parameters: Parameters) -> Self::Rooted;
}

const DEFAULT_HEAP_COLLECT_THRESHOLD: usize = 1 << 20;
const DEFAULT_HEAP_GROW_PERCENT: u8 = 50;

pub struct Parameters {
    collect_threshold: usize,
    grow_percent: u8,
}

pub struct Heap {
    gray: Vec<NonNull<Header>>,
    head: Cell<Option<NonNull<Header>>>,
    size: usize,
    parameters: Parameters,
}

#[repr(C)]
pub struct Header {
    kind: ObjectKind,
    marked: Cell<bool>,
    next: Cell<Option<NonNull<Header>>>,
}

#[non_exhaustive]
pub struct MutationContext<'gc, R: Root> {
    pub root: &'gc mut R,
}

pub struct AllocationContext<'gc, R: Root> {
    pub root: &'gc mut R,
    heap: &'gc mut Heap,
}

#[allow(dead_code)]
#[repr(C)]
pub struct Box<T: Managed> {
    header: Header,
    data: T,
}

/// Smart pointer to `Managed` objects.
pub struct Gc<'gc, T: Managed> {
    ptr: NonNull<T>,
    _marker: PhantomData<&'gc ()>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
#[repr(u8)]
pub enum ObjectKind {
    Blank,
    String,
    Pair,
    Vector,
    Closure,
    Function,
}

type Blank = ();

macro_rules! trace_object {
    ( $ptr:expr; $tracer:expr; $( $ki:ident, )+ ) => {
        match $ptr.cast::<Header>().as_ref().kind() {
            $(
                ObjectKind::$ki => {
                    trace_box::<$ki, _>($ptr, &mut $tracer);
                }
            )+
        }
    };
}

macro_rules! free_object {
    ( $ptr:expr; $( $ki:ident, )+ ) => {
        match $ptr.cast::<Header>().as_ref().kind() {
            $(
                ObjectKind::$ki => {
                    free_box::<$ki>($ptr)
                }
            )+
        }
    };
}

impl Parameters {
    #[inline]
    pub const fn zealous() -> Self {
        Self {
            collect_threshold: 0,
            grow_percent: 0,
        }
    }

    #[inline]
    pub const fn idle() -> Self {
        Self {
            collect_threshold: usize::MAX,
            grow_percent: 0,
        }
    }
}

impl Default for Parameters {
    fn default() -> Self {
        Self {
            collect_threshold: DEFAULT_HEAP_COLLECT_THRESHOLD,
            grow_percent: DEFAULT_HEAP_GROW_PERCENT,
        }
    }
}

impl Heap {
    #[inline]
    pub const fn with_parameters(parameters: Parameters) -> Self {
        Self {
            gray: vec![],
            head: Cell::new(None),
            size: 0,
            parameters,
        }
    }

    #[inline]
    fn should_collect(&self) -> bool {
        self.size >= self.parameters.collect_threshold
    }

    #[inline]
    fn mark(&mut self) {
        while let Some(ptr) = self.gray.pop() {
            unsafe {
                trace_object! {
                    ptr; self.gray;
                    Blank,
                    String,
                    Pair,
                    Vector,
                    Closure,
                    Function,
                };
            }
        }
    }

    #[inline]
    fn sweep(&mut self) -> usize {
        let mut next = &self.head;
        let mut freed = 0;

        while let Some(ptr) = next.get() {
            unsafe {
                let header = &*ptr.as_ptr();

                if header.marked.get() {
                    header.marked.set(false);
                    next = &header.next;
                } else {
                    next.set(header.next.get());

                    log::trace!("freed {}: {:?}", ptr.cast::<Header>().as_ref().kind, ptr);

                    freed += free_object! {
                        ptr;
                        Blank,
                        String,
                        Pair,
                        Vector,
                        Closure,
                        Function,
                    };
                }
            }
        }

        self.size -= freed;
        self.parameters.collect_threshold =
            self.size + self.size / 100 * self.parameters.grow_percent as usize;

        freed
    }
}

impl Drop for Heap {
    #[inline]
    fn drop(&mut self) {
        // No marking phase, so sweep should drop all objects.
        self.sweep();
        assert!(self.size == 0);
    }
}

impl Header {
    #[inline]
    pub const fn kind(&self) -> ObjectKind {
        self.kind
    }
}

impl<'gc, R> MutationContext<'gc, R>
where
    R: Root,
{
    #[doc(hidden)]
    pub unsafe fn for_root(root: &'gc mut R) -> MutationContext<'gc, R> {
        MutationContext { root }
    }
}

impl<'gc, R> AllocationContext<'gc, R>
where
    R: Root,
{
    #[doc(hidden)]
    pub unsafe fn for_root(root: &'gc mut R, heap: &'gc mut Heap) -> AllocationContext<'gc, R> {
        AllocationContext { root, heap }
    }

    /// Allocates a new managed object.
    pub fn alloc<T>(&mut self, data: T) -> Gc<'gc, T>
    where
        T: Managed,
    {
        unsafe {
            let ptr = alloc_box(Box {
                header: Header {
                    kind: T::KIND,
                    marked: Cell::new(false),
                    next: self.heap.head.clone(),
                },
                data,
            });

            self.heap.head.set(Some(ptr));
            self.heap.size += size_of::<Box<T>>();

            log::trace!("alloc {}: {:?}", T::KIND, ptr);

            Gc {
                ptr: header_to_data(ptr),
                _marker: PhantomData,
            }
        }
    }

    pub fn alloc_list<I>(&mut self, values: I) -> Value<'gc>
    where
        I: ExactSizeIterator<Item = Value<'gc>> + DoubleEndedIterator<Item = Value<'gc>>,
    {
        let mut tail = Value::NIL;

        for next in values.rev() {
            tail = self.alloc(Pair::new(next, tail)).into();
        }

        tail
    }

    #[inline]
    fn maybe_collect(&mut self) -> usize {
        if self.heap.should_collect() {
            self.collect()
        } else {
            0
        }
    }

    fn collect(&mut self) -> usize {
        self.root.trace(&mut self.heap.gray);
        self.heap.mark();
        self.heap.sweep()
    }
}

impl<'gc, R> Drop for AllocationContext<'gc, R>
where
    R: Root,
{
    #[inline(always)]
    fn drop(&mut self) {
        self.maybe_collect();
    }
}

#[repr(transparent)]
struct UnsafeStatic(Box<()>);

unsafe impl Sync for UnsafeStatic {}

static UNUSED: UnsafeStatic = UnsafeStatic(Box {
    header: Header {
        kind: ObjectKind::Blank,
        marked: Cell::new(true),
        next: Cell::new(None),
    },
    data: (),
});

impl<'gc, T> Gc<'gc, T>
where
    T: Managed,
{
    /// Creates a `Gc` pointer that is dangling. This is useful for initializing
    /// types which lazily allocate.
    ///
    /// # Safety
    /// This `Gc` is safe to copy and safe to be traced, but it must not be
    /// dereferenced. There is no reliable way to check if a `Gc` pointer is
    /// dangling, so this must not be used as a "not yet initialized" sentinel
    /// value. Types that lazily allocate must track initialization by
    /// some other means.
    #[inline]
    pub unsafe fn dangling() -> Self {
        Self::from_ptr(header_to_data(NonNull::from(&UNUSED).cast::<Header>()))
    }

    pub(crate) unsafe fn from_ptr(ptr: NonNull<T>) -> Self {
        Self {
            ptr,
            _marker: PhantomData,
        }
    }

    pub(crate) fn as_ptr(&self) -> NonNull<T> {
        self.ptr
    }
}

impl<'gc, T> Clone for Gc<'gc, T>
where
    T: Managed,
{
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
            _marker: PhantomData,
        }
    }
}

impl<'gc, T> Copy for Gc<'gc, T> where T: Managed {}

impl<'gc, T> AsRef<T> for Gc<'gc, T>
where
    T: Managed,
{
    fn as_ref(&self) -> &T {
        unsafe { &*self.ptr.as_ptr() }
    }
}

impl<'gc, T> Deref for Gc<'gc, T>
where
    T: Managed,
{
    type Target = T;

    fn deref(&self) -> &T {
        self.as_ref()
    }
}

impl<'gc, T> Borrow<T> for Gc<'gc, T>
where
    T: Managed,
{
    fn borrow(&self) -> &T {
        self.as_ref()
    }
}

impl<'gc, T> PartialEq for Gc<'gc, T>
where
    T: Managed + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.as_ref().eq(other.as_ref())
    }
}

impl<'gc, T> Eq for Gc<'gc, T> where T: Managed + Eq {}

impl<'gc, T> Debug for Gc<'gc, T>
where
    T: Managed + Debug,
{
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
        self.as_ref().fmt(fmt)
    }
}

unsafe impl<'gc, T> Trace for Gc<'gc, T>
where
    T: Managed,
{
    fn trace(&self, tracer: &mut impl Tracer) {
        tracer.mark(unsafe { data_to_header(self.ptr) })
    }
}

pub trait Managed: Trace + sealed::Managed {}
impl<T: Trace + sealed::Managed> Managed for T {}

#[inline]
pub(crate) unsafe fn data_to_header<T>(ptr: NonNull<T>) -> NonNull<Header>
where
    T: Managed,
{
    NonNull::new_unchecked(ptr.cast::<Header>().as_ptr().wrapping_sub(1) as *mut _)
}

#[inline]
pub(crate) unsafe fn header_to_data<T>(ptr: NonNull<Header>) -> NonNull<T>
where
    T: Managed,
{
    NonNull::new_unchecked(ptr.as_ptr().wrapping_add(1) as *mut _)
}

#[inline]
unsafe fn alloc_box<T>(data: Box<T>) -> NonNull<Header>
where
    T: Managed,
{
    use std::boxed::Box as StdBox;
    NonNull::new_unchecked(StdBox::into_raw(StdBox::new(data)) as *mut Header)
}

#[inline]
unsafe fn trace_box<T, U>(ptr: NonNull<Header>, tracer: &mut U)
where
    T: Managed,
    U: Tracer,
{
    header_to_data::<T>(ptr).as_ref().trace(tracer);
}

#[inline]
unsafe fn free_box<T>(ptr: NonNull<Header>) -> usize
where
    T: Managed,
{
    use std::boxed::Box as StdBox;
    drop(StdBox::from_raw(ptr.cast::<Box<T>>().as_ptr()));
    size_of::<Box<T>>()
}

pub trait Tracer: sealed::Tracer {}
impl<T> Tracer for T where T: sealed::Tracer {}

impl Display for ObjectKind {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
        match self {
            ObjectKind::Blank => write!(fmt, "blank object"),
            ObjectKind::String => write!(fmt, "string"),
            ObjectKind::Pair => write!(fmt, "pair"),
            ObjectKind::Vector => write!(fmt, "vector"),
            ObjectKind::Closure => write!(fmt, "closure"),
            ObjectKind::Function => write!(fmt, "function"),
        }
    }
}

mod sealed {
    use super::*;

    pub unsafe trait Managed {
        const KIND: ObjectKind;
    }

    pub trait Tracer {
        fn mark(&mut self, ptr: NonNull<Header>);
    }

    unsafe impl Managed for () {
        const KIND: ObjectKind = ObjectKind::Blank;
    }

    unsafe impl Managed for String {
        const KIND: ObjectKind = ObjectKind::String;
    }

    unsafe impl<'gc> Managed for Pair<'gc> {
        const KIND: ObjectKind = ObjectKind::Pair;
    }

    unsafe impl<'gc> Managed for Vector<'gc> {
        const KIND: ObjectKind = ObjectKind::Vector;
    }

    unsafe impl<'gc> Managed for Closure<'gc> {
        const KIND: ObjectKind = ObjectKind::Closure;
    }

    unsafe impl<'gc> Managed for Function {
        const KIND: ObjectKind = ObjectKind::Function;
    }

    impl Tracer for Vec<NonNull<Header>> {
        fn mark(&mut self, ptr: NonNull<Header>) {
            unsafe { ptr.as_ref() }.marked.set(true);
            self.push(ptr);
        }
    }
}
