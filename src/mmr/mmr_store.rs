use ark_std::vec::Vec;
use super::error::{Result, Error};

#[derive(Default)]
pub struct MMRBatch<Elem> {
    memory_batch: Vec<(u64, Vec<Elem>)>,
    // store: Store,
}

impl<Elem: Clone> MMRBatch<Elem> {
    pub fn new() -> Self {
        MMRBatch {
            memory_batch: Vec::new(),
            // store,
        }
    }

    pub fn clone(&self) -> Self {
        MMRBatch {
            memory_batch: self.memory_batch.clone(),
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
        Err(Error::InvalidArgument)
    }

    // pub fn commit(self) -> Result<()> {
    //     let Self {
    //         mut store,
    //         memory_batch,
    //     } = self;
    //     for (pos, elems) in memory_batch {
    //         store.append(pos, elems)?;
    //     }
    //     Ok(())
    // }
}

// impl<Elem, Store: MMRStore<Elem>> IntoIterator for MMRBatch<Elem, Store> {
//     type Item = (u64, Vec<Elem>);
//     type IntoIter = ark_std::vec::IntoIter<Self::Item>;

//     fn into_iter(self) -> Self::IntoIter {
//         self.memory_batch.into_iter()
//     }
// }

// pub trait MMRStore<Elem> {
//     fn get_elem(&self, pos: u64) -> Result<Option<Elem>>;
//     fn append(&mut self, pos: u64, elems: Vec<Elem>) -> Result<()>;
// }
