use ark_std::vec::Vec;
use super::error::{Result, Error};

#[derive(Default)]
pub struct MMRBatch<Elem> {
    memory_batch: Vec<(u64, Vec<Elem>)>,
}

impl<Elem: Clone> MMRBatch<Elem> {
    pub fn new() -> Self {
        MMRBatch {
            memory_batch: Vec::new(),
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

}
