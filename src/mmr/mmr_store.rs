use ark_std::vec::Vec;
use super::{error::Result};
use std::{collections::BTreeMap};
use core::cell::RefCell;

pub struct MMRBatch<Elem> {
    memory_batch: Vec<(u64, Vec<Elem>)>,
    store: MemStore<Elem>,

}

impl<Elem: Clone> MMRBatch<Elem> {
    pub fn new() -> Self {
        MMRBatch {
            memory_batch: Vec::new(),
            store: MemStore::new(),
        }
    }


    pub fn append(&mut self, pos: u64, elems: Vec<Elem>) {
        self.memory_batch.push((pos, elems));
    }

    pub fn get_elem(&self, pos: u64) -> Result<Option<Elem>> {
        for (start_pos, elems) in self.memory_batch.iter().rev() {
            if pos < *start_pos {
                continue;
            } else if pos < start_pos + elems.len() as u64 {
                return Ok(elems.get((pos - start_pos) as usize).cloned());
            } else {
                break;
            }
        }
        self.store.get_elem(pos)
    }

    pub fn commit(self) -> Result<()> {
        let Self { mut store, memory_batch } = self;
        for (pos, elems) in memory_batch {
            store.append(pos, elems)?;
        }
        Ok(())
    }

}

impl<Elem> IntoIterator for MMRBatch<Elem> {
    type Item = (u64, Vec<Elem>);
    type IntoIter = ark_std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.memory_batch.into_iter()
    }
}

pub struct MemStore<T>{
    map: RefCell<BTreeMap<u64, T>>
}

impl<T> Default for MemStore<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> MemStore<T> {
    pub fn new() -> Self {
        MemStore{
            map: RefCell::new(Default::default())
        }
    }
}

impl<T: Clone> MMRStore<T> for MemStore<T> {
    fn new() -> Result<Self> {
        Ok(MemStore{
            map: RefCell::new(Default::default())
            }
        )
    }

    fn get_elem(&self, pos: u64) -> Result<Option<T>> {
        // println!("store require: {:#?}", pos);

        Ok(self.map.borrow().get(&pos).cloned())
    }

    fn append(&mut self, pos: u64, elems: Vec<T>) -> Result<()> {
        let mut store = self.map.borrow_mut();
        for (i, elem) in elems.into_iter().enumerate() {
            store.insert(pos + i as u64, elem);
        }
        Ok(())
    }

    fn clone(&self) -> Result<Self> {
        Ok(MemStore {
            map: RefCell::new(self.map.clone().into_inner())
        })
    }
}

impl<T: Clone> Clone for MemStore<T> {
    fn clone(&self) -> MemStore<T> {
        MemStore {
            map: RefCell::new(self.map.clone().into_inner())
        }
    }
}

pub trait MMRStore<Elem>: Clone + Sized {
    fn new() -> Result<Self> where Self: Sized;
    fn get_elem(&self, pos: u64) -> Result<Option<Elem>>;
    fn append(&mut self, pos: u64, elems: Vec<Elem>) -> Result<()>;
    fn clone(&self) -> Result<Self> where Self: Sized;
}
