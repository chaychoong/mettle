//! Typed-index arenas: the one object-graph representation used by every IR.
//!
//! All ASTs/IRs in mettle are `Vec`-backed arenas addressed by `u32` newtype
//! IDs (STYLE §6, `PORTING_RULES` R3). Cross-references between nodes are IDs
//! resolved through the owning arena — never `Rc<RefCell<..>>` graphs, never
//! references with lifetimes threaded through node types. The ID's type names
//! the arena it belongs to (STYLE A4): an `ExprId` only indexes the `Expr`
//! arena, and mixing IDs across arenas is a type error.

use std::fmt;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

/// A dense `u32`-backed index into exactly one [`Arena`].
///
/// Implemented via [`define_id!`]; not intended for manual implementation.
pub trait ArenaId: Copy + Eq {
    /// Wraps a raw arena index.
    ///
    /// # Panics
    /// Panics if `index` exceeds `u32::MAX` — arenas are u32-dense by design,
    /// and overflowing that is an internal invariant violation, not user error.
    fn from_index(index: usize) -> Self;

    /// The raw index this ID wraps.
    fn index(self) -> usize;
}

/// Defines a `u32`-backed newtype ID implementing [`ArenaId`].
///
/// ```
/// als_syntax::define_id! {
///     /// Index into the widget arena.
///     pub struct WidgetId;
/// }
/// ```
#[macro_export]
macro_rules! define_id {
    ($(#[$meta:meta])* $vis:vis struct $name:ident;) => {
        $(#[$meta])*
        #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
        $vis struct $name(u32);

        impl $crate::ArenaId for $name {
            fn from_index(index: usize) -> Self {
                let Ok(raw) = u32::try_from(index) else {
                    panic!("arena index overflow: {index}");
                };
                Self(raw)
            }

            fn index(self) -> usize {
                self.0 as usize
            }
        }

        impl ::std::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                write!(f, concat!(stringify!($name), "({})"), self.0)
            }
        }
    };
}

/// An append-only, `u32`-indexed store of `T`, addressed by the ID type `I`.
///
/// Allocation order is the iteration order — deterministic by construction
/// (STYLE D2 does not apply: there is no hashing anywhere).
pub struct Arena<I, T> {
    items: Vec<T>,
    _id: PhantomData<fn(I) -> I>,
}

impl<I: ArenaId, T> Arena<I, T> {
    /// Creates an empty arena.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            items: Vec::new(),
            _id: PhantomData,
        }
    }

    /// Appends `item` and returns its freshly minted ID.
    pub fn alloc(&mut self, item: T) -> I {
        let id = I::from_index(self.items.len());
        self.items.push(item);
        id
    }

    /// Number of items allocated.
    #[must_use]
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Whether nothing has been allocated yet.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Iterates `(id, item)` pairs in allocation order.
    pub fn iter(&self) -> impl Iterator<Item = (I, &T)> {
        self.items
            .iter()
            .enumerate()
            .map(|(index, item)| (I::from_index(index), item))
    }
}

impl<I: ArenaId, T> Default for Arena<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: ArenaId, T> Index<I> for Arena<I, T> {
    type Output = T;

    fn index(&self, id: I) -> &T {
        &self.items[id.index()]
    }
}

impl<I: ArenaId, T> IndexMut<I> for Arena<I, T> {
    fn index_mut(&mut self, id: I) -> &mut T {
        &mut self.items[id.index()]
    }
}

impl<I: ArenaId, T: fmt::Debug> fmt::Debug for Arena<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(&self.items).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    define_id! {
        /// Test-only ID.
        struct TestId;
    }

    #[test]
    fn alloc_get_roundtrip() {
        let mut arena: Arena<TestId, &str> = Arena::new();
        let a = arena.alloc("a");
        let b = arena.alloc("b");
        assert_eq!(arena[a], "a");
        assert_eq!(arena[b], "b");
        assert_eq!(arena.len(), 2);
    }

    #[test]
    fn iter_is_allocation_order() {
        let mut arena: Arena<TestId, u8> = Arena::new();
        let ids: Vec<TestId> = (0u8..4).map(|n| arena.alloc(n)).collect();
        let seen_ids: Vec<TestId> = arena.iter().map(|(id, _)| id).collect();
        let seen_values: Vec<u8> = arena.iter().map(|(_, &n)| n).collect();
        assert_eq!(seen_ids, ids);
        assert_eq!(seen_values, vec![0, 1, 2, 3]);
    }

    #[test]
    fn id_index_roundtrip() {
        let id = TestId::from_index(7);
        assert_eq!(id.index(), 7);
        assert_eq!(format!("{id:?}"), "TestId(7)");
    }
}
