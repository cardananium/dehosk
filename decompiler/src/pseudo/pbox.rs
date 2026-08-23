//! Owning containers whose destructor is iterative.
//!
//! `Box`'s and `Vec`'s destructors are structurally recursive — one call frame
//! per level of nesting — and the nesting depth of a decompiled tree is
//! script-controlled. On `wasm32` that overflows the engine's call stack,
//! which cannot be grown from the page, and it does so while the tree is being
//! *released*, after all the real work already succeeded.
//!
//! The tree types themselves cannot implement `Drop`: they are destructured by
//! value throughout the decompiler (~2400 sites for `PseudoExpr` alone), and a
//! type that implements `Drop` cannot be moved out of. Putting the destructor
//! on the containers instead moves it onto types nothing destructures.

/// A tree node that can hand over its children.
///
/// The contract [`Owned`] and [`OwnedVec`] rely on: after `take_children`, the
/// node holds no further nodes, so dropping it cannot recurse.
pub(crate) trait Nested: Sized {
    /// Replace this node's children with cheap placeholders and return them.
    fn take_children(&mut self) -> Vec<Self>;
}

/// Release a whole forest without recursing.
///
/// Each node is emptied before it goes out of scope, so the implicit drop at
/// the end of the loop body only ever frees a childless node.
fn release_all<T: Nested>(mut stack: Vec<T>) {
    while let Some(mut node) = stack.pop() {
        stack.append(&mut node.take_children());
    }
}

/// `Box<T>` with an iterative destructor.
pub(crate) struct Owned<T: Nested>(std::boxed::Box<T>);

impl<T: Nested> Owned<T> {
    pub(crate) fn new(inner: T) -> Self {
        Owned(std::boxed::Box::new(inner))
    }

    /// Take the value out, consuming the pointer.
    pub(crate) fn into_inner(self) -> T {
        // `Self` implements `Drop`, so the field cannot simply be moved out.
        let this = std::mem::ManuallyDrop::new(self);
        // SAFETY: `this` is never dropped and the field is never read again —
        // `ManuallyDrop` suppresses the destructor that would otherwise run.
        let boxed = unsafe { std::ptr::read(&this.0) };
        *boxed
    }
}

impl<T: Nested> Drop for Owned<T> {
    fn drop(&mut self) {
        release_all(self.0.take_children());
    }
}

/// `Vec<T>` with an iterative destructor.
pub(crate) struct OwnedVec<T: Nested>(Vec<T>);

impl<T: Nested> Default for OwnedVec<T> {
    fn default() -> Self {
        OwnedVec(Vec::new())
    }
}

impl<T: Nested> OwnedVec<T> {
    pub(crate) fn new() -> Self {
        OwnedVec(Vec::new())
    }

    /// Take the elements out, leaving this empty.
    pub(crate) fn take(&mut self) -> Vec<T> {
        std::mem::take(&mut self.0)
    }

    pub(crate) fn into_vec(self) -> Vec<T> {
        let this = std::mem::ManuallyDrop::new(self);
        // SAFETY: as in `Owned::into_inner`.
        unsafe { std::ptr::read(&this.0) }
    }
}

impl<T: Nested> Drop for OwnedVec<T> {
    fn drop(&mut self) {
        release_all(std::mem::take(&mut self.0));
    }
}

// ---------------------------------------------------------------------------
// Pass-through impls, so the containers stand in for `Box` / `Vec` at use
// sites without touching them.
// ---------------------------------------------------------------------------

impl<T: Nested> std::ops::Deref for Owned<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T: Nested> std::ops::DerefMut for Owned<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T: Nested> AsRef<T> for Owned<T> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T: Nested> AsMut<T> for Owned<T> {
    fn as_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T: Nested> std::borrow::Borrow<T> for Owned<T> {
    fn borrow(&self) -> &T {
        &self.0
    }
}

impl<T: Nested> From<T> for Owned<T> {
    fn from(inner: T) -> Self {
        Owned::new(inner)
    }
}

impl<T: Nested + std::fmt::Debug> std::fmt::Debug for Owned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: Nested + Clone> Clone for Owned<T> {
    fn clone(&self) -> Self {
        Owned::new((*self.0).clone())
    }
}

impl<T: Nested + PartialEq> PartialEq for Owned<T> {
    fn eq(&self, other: &Self) -> bool {
        *self.0 == *other.0
    }
}

impl<T: Nested + Eq> Eq for Owned<T> {}

impl<T: Nested> std::ops::Deref for OwnedVec<T> {
    type Target = Vec<T>;
    fn deref(&self) -> &Vec<T> {
        &self.0
    }
}

impl<T: Nested> std::ops::DerefMut for OwnedVec<T> {
    fn deref_mut(&mut self) -> &mut Vec<T> {
        &mut self.0
    }
}

impl<T: Nested> From<Vec<T>> for OwnedVec<T> {
    fn from(items: Vec<T>) -> Self {
        OwnedVec(items)
    }
}

impl<T: Nested> FromIterator<T> for OwnedVec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        OwnedVec(iter.into_iter().collect())
    }
}

impl<T: Nested> IntoIterator for OwnedVec<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        self.into_vec().into_iter()
    }
}

impl<'a, T: Nested> IntoIterator for &'a OwnedVec<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a, T: Nested> IntoIterator for &'a mut OwnedVec<T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl<T: Nested + std::fmt::Debug> std::fmt::Debug for OwnedVec<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: Nested + Clone> Clone for OwnedVec<T> {
    fn clone(&self) -> Self {
        OwnedVec(self.0.clone())
    }
}

impl<T: Nested + PartialEq> PartialEq for OwnedVec<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: Nested + Eq> Eq for OwnedVec<T> {}
