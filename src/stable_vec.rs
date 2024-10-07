
use std::{marker::PhantomData, vec::IntoIter};

use super::*;


/// Index to an existing value inside a StableVec
pub struct StableVecID<T> { val : usize, pub phantom : PhantomData<T> }

impl<T> StableVecID<T>
{
    pub const fn new(val:usize) -> Self { Self { val, phantom: PhantomData }}
    pub fn value(&self) -> usize { self.val }
}

impl<T> Clone for StableVecID<T>{ fn clone(&self) -> Self { *self }}
impl<T> Copy for StableVecID<T>{}
impl<T> Debug for StableVecID<T> { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "#{}", self.val) }}
impl<T> PartialEq for StableVecID<T> { fn eq(&self, other: &Self) -> bool { self.val == other.val }}
impl<T> Eq for StableVecID<T> {}
impl<T> std::hash::Hash for StableVecID<T>{ fn hash<H: std::hash::Hasher>(&self, state: &mut H) { self.val.hash(state); }}


/// A vector where entry are stable (even when deleting element)
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct StableVec<T>
{
    // Indexed by FlattenTreeID<T>. Index are stable. Root is 0.
    pub values : Vec<Option<T>>,
    /// Index of the removed T that can be recycled.
    pub free_slot : Vec<StableVecID<T>>,
}

impl<T> Default for StableVec<T> { fn default() -> Self { Self { values: ___(), free_slot: ___() } }}

impl<T> std::iter::IntoIterator for StableVec<T> {
    type Item = T;
    type IntoIter = std::iter::Flatten<std::vec::IntoIter<Option<T>>>;

    fn into_iter(self) -> Self::IntoIter {
        self.values.into_iter().flatten()
    }
}

impl<T> StableVec<T>
{
    pub fn iter(&self) -> impl Iterator<Item=&T> + '_ { self.values.iter().flatten() }
    pub fn iter_mut(&mut self) -> impl Iterator<Item=&mut T> + '_ { self.values.iter_mut().flatten() }

    pub fn iter_with_key(&self) -> impl Iterator<Item=(StableVecID<T>, &T)> + '_ 
    { 
        self.values
        .iter()
        .enumerate()
        .filter_map(|(idx, e)| { e.as_ref().map(|v| (StableVecID::<T>::new(idx), v)) }) 
    }

    pub fn iter_mut_with_key(&mut self) -> impl Iterator<Item=(StableVecID<T>, &mut T)> + '_ 
    { 
        self.values
        .iter_mut()
        .enumerate()
        .filter_map(|(idx, e)| { e.as_mut().map(|v| (StableVecID::<T>::new(idx), v)) }) 
    }

    pub fn push(&mut self, val : T) -> StableVecID<T>
    {
        let idx = self.free_slot.pop().map(|e| e.val).unwrap_or_else(|| { self.values.push(None); self.values.len()-1});
        self.values[idx] = Some(val);
        StableVecID::new(idx)
    }

    pub fn pop(&mut self, id : StableVecID<T>)
    {
        debug_assert!(self.values[id.val].is_some());
        self.values[id.val] = None;
        self.free_slot.push(id);
    }

    pub fn remove(&mut self, id : StableVecID<T>) -> T
    {
        self.free_slot.push(id);
        self.values[id.val].take().unwrap()
    }

    pub fn len(&self) -> usize { self.values.len() - self.free_slot.len() }
    pub fn is_empty(&self) -> bool { self.len() == 0 }
}

impl<T> Index<StableVecID<T>> for StableVec<T>
{
    type Output=T;
    fn index(&self, index: StableVecID<T>) -> &Self::Output { self.values[index.val].as_ref().unwrap() }
}
impl<T> IndexMut<StableVecID<T>> for StableVec<T>
{
    fn index_mut(&mut self, index: StableVecID<T>) -> &mut Self::Output { self.values[index.val].as_mut().unwrap() }
}