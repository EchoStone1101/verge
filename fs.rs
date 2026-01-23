use vstd::prelude::*;
use std::path::Path;
use std::io::SeekFrom;
use std::os::fd::AsRawFd;
use std::io::Seek;
use std::collections::HashMap;

mod std_fs;

verus! {

use std_fs::{
    StdFile, IoError, file_exists, 
};

uninterp spec fn get_file_content(file: &String, i: int) -> u8;
pub uninterp spec fn is_different_file(file1: &String, file2: &String) -> bool;

#[verifier::external_body]
pub struct GlobalOpenFilesInner {
    open_files: HashMap<(u64, u64), ()>,
}

impl GlobalOpenFilesInner {
    #[verifier::external_body]
    fn new() -> Self {
        GlobalOpenFilesInner {
            open_files: HashMap::new(),
        }
    }

    #[verifier::external_body]
    fn contains_key(&self, k: &(u64, u64)) -> bool {
        self.open_files.contains_key(k)
    }

    #[verifier::external_body]
    fn insert(&mut self, k: (u64, u64)) {
        self.open_files.insert(k, ());
    }

    #[verifier::external_body]
    fn remove(&mut self, k: &(u64, u64)) {
        self.open_files.remove(k);
    }
}

pub struct GlobalOpenFiles {
    pub open_files: GlobalOpenFilesInner,
    /// A ghost set of all files, including those that are closed
    pub ghost_files: Ghost<Set<String>>,
}

impl GlobalOpenFiles {
    pub fn new() -> (s: Self) 
        ensures s.ghost_files@.is_empty()
    {
        Self {
            open_files: GlobalOpenFilesInner::new(),
            ghost_files: Ghost(Set::empty()),
        }
    }

    #[verifier::external_body]
    fn open_checked(&mut self, open_result: Result<(StdFile, Ghost<nat>), FileError>, path: &String) -> (result: Result<(StdFile, Ghost<nat>), FileError>) 
        requires
            forall |p: String| #![auto] old(self).ghost_files@.contains(p) ==> {
                !is_different_file(&p, &p) && old(self).ghost_files@.filter(|q| !is_different_file(&q, &p)).len() == 1
            },  
        ensures 
            !is_different_file(path, path),
            forall |p: String| #![auto] self.ghost_files@.contains(p) ==> {
                !is_different_file(&p, &p) && self.ghost_files@.filter(|q| !is_different_file(&q, &p)).len() == 1
            },
            match result {
                Ok((_, file_len)) => {
                    &&& old(self).ghost_files@.insert(*path) == self.ghost_files@ 
                    &&& forall |p: String| #![auto] old(self).ghost_files@.contains(p) ==> is_different_file(&p, &path) && is_different_file(&path, &p)
                    &&& 0 <= file_len@ <= i64::MAX
                },
                Err(FileError::AlreadyOpen) => {
                    &&& old(self).ghost_files@ =~= self.ghost_files@ 
                    &&& exists |p: String| #![auto] self.ghost_files@.contains(p) && !is_different_file(&p, &path) && !is_different_file(&path, &p)
                },
                Err(_) => old(self).ghost_files@ =~= self.ghost_files@,
            }
    {
        let Ok((file, file_len)) = open_result else {
            return open_result;
        };
        let metadata = file.metadata().map_err(FileError::new)?;
        let key = (metadata.dev(), metadata.ino());
        let is_open = self.open_files.contains_key(&key);

        if is_open {
            Err(FileError::already_open())
        }
        else {
            self.open_files.insert(key);
            Ok((file, file_len))
        }
    }

    #[verifier::external_body]
    /// Check if the file is already open (when it exists)
    fn create_checked(&self, path: &String) -> Result<(), FileError> {
        let is_exist = file_exists(path).map_err(FileError::new)?;
        if !is_exist {
            return Ok(());
        }
        let Ok((std_file, _)) = StdFile::open(path) else {
            return Ok(());
        };

        let metadata = std_file.metadata().map_err(FileError::new)?;
        let key = (metadata.dev(), metadata.ino());
        let is_open = self.open_files.contains_key(&key);

        if is_open {
            Err(FileError::already_open())
        }
        else {
            Ok(())
        }
    }
    
    #[verifier::external_body]
    fn close(&mut self, std_file: &StdFile) -> (result: Result<(), FileError>) 
        requires
            forall |p: String| #![auto] old(self).ghost_files@.contains(p) ==> {
                !is_different_file(&p, &p) && old(self).ghost_files@.filter(|q| !is_different_file(&q, &p)).len() == 1
            },  
        ensures 
            old(self).ghost_files@ =~= self.ghost_files@,
            forall |p: String| #![auto] self.ghost_files@.contains(p) ==> {
                !is_different_file(&p, &p) && self.ghost_files@.filter(|q| !is_different_file(&q, &p)).len() == 1
            },
    {
        let metadata = std_file.metadata().map_err(FileError::new)?;
        let key = (metadata.dev(), metadata.ino());
        self.open_files.remove(&key);
        Ok(())
    }
}

/// A verified file handle that tracks the file's state
pub struct VerifiedFile {
    pub inner: StdFile,
    pub virtual_file: Ghost<VirtualFile>,
}

pub ghost struct VirtualFile {
    pub content: Seq<u8>,
    pub pos: nat,
    pub file_len: nat,
}

impl VirtualFile {
    spec fn build(file_len: nat, content: Seq<u8>) -> VirtualFile
        recommends
            content.len() == file_len,
    {
        VirtualFile {
            content,
            pos: 0,
            file_len,
        }
    }
}

pub enum FileError {
    IoError(IoError),
    // Other error variants can be added here
    Other,
    AlreadyOpen,
}

impl FileError {
    pub fn new(io_err: IoError) -> Self {
        FileError::IoError(io_err)
    }

    pub fn empty() -> Self {
        FileError::Other
    }

    pub fn already_open() -> Self {
        FileError::AlreadyOpen
    }
}

impl VerifiedFile {
    /// Opens a file for reading and writing, but only if it is not already open.
    pub fn open(path: &String, global_open_files: &mut GlobalOpenFiles) -> (result: Result<VerifiedFile, FileError>)
        requires
            forall |p: String| #![auto] old(global_open_files).ghost_files@.contains(p) ==> {
                !is_different_file(&p, &p) && old(global_open_files).ghost_files@.filter(|q| !is_different_file(&q, &p)).len() == 1
            }
        ensures
            forall |p: String| #![auto] global_open_files.ghost_files@.contains(p) ==> {
                !is_different_file(&p, &p) && global_open_files.ghost_files@.filter(|q| !is_different_file(&q, &p)).len() == 1
            }, 
            match result {
                Ok(f) => {
                    let vf = f.virtual_file@;
                    vf.pos == 0 && vf.file_len == vf.content.len() && 0 <= vf.file_len <= i64::MAX
                    && old(global_open_files).ghost_files@.insert(*path) == global_open_files.ghost_files@ 
                    && forall |p: String| #![auto] old(global_open_files).ghost_files@.contains(p) ==> is_different_file(&p, &path) && is_different_file(&path, &p)
                },
                Err(FileError::AlreadyOpen) => {
                    old(global_open_files).ghost_files@ =~= global_open_files.ghost_files@
                    && exists |p: String| #![auto] global_open_files.ghost_files@.contains(p) && !is_different_file(&p, &path) && !is_different_file(&path, &p)
                },
                // Note: not handle error in StdFile yet
                Err(_) => old(global_open_files).ghost_files@ =~= global_open_files.ghost_files@,
            },
    {
        let open_result = StdFile::open(path).map_err(FileError::new);

        let (file, file_len) = match global_open_files.open_checked(open_result, path) {
            Ok((file, file_len)) => (file, file_len),
            Err(e) => {
                // Note: can not remove this assert
                assert(
                    forall |p: String| #![auto] global_open_files.ghost_files@.contains(p) ==> {
                        !is_different_file(&p, &p) && global_open_files.ghost_files@.filter(|q| !is_different_file(&q, &p)).len() == 1
                    }
                );                
                return Err(e)
            },
        };

        let ghost file_len = file_len@;
        let ghost content = Seq::new(file_len, |i: int| get_file_content(path, i));
        let virtual_file = Ghost(VirtualFile::build(file_len, content));
        
        Ok(VerifiedFile {
            inner: file,
            virtual_file,
        })
    }

    /// Creates a new file or truncates an existing one
    #[verifier::external_body]
    pub fn create(path: &String, global_open_files: &mut GlobalOpenFiles) -> (result: Result<VerifiedFile, FileError>)
        requires
            forall |p: String| #![auto] old(global_open_files).ghost_files@.contains(p) ==> {
                !is_different_file(&p, &p) && old(global_open_files).ghost_files@.filter(|q| !is_different_file(&q, &p)).len() == 1
            }
        ensures
            forall |p: String| #![auto] global_open_files.ghost_files@.contains(p) ==> {
                !is_different_file(&p, &p) && global_open_files.ghost_files@.filter(|q| !is_different_file(&q, &p)).len() == 1
            }, 
            match result {
                Ok(f) => {
                    let vf = f.virtual_file@;
                    vf.pos == 0 && vf.file_len == 0 && vf.content.len() == 0
                    && old(global_open_files).ghost_files@.insert(*path) == global_open_files.ghost_files@ 
                    && forall |p: String| #![auto] old(global_open_files).ghost_files@.contains(p) ==> is_different_file(&p, &path) && is_different_file(&path, &p)
                },
                Err(FileError::AlreadyOpen) => {
                    old(global_open_files).ghost_files@ =~= global_open_files.ghost_files@
                    && exists |p: String| #![auto] global_open_files.ghost_files@.contains(p) && !is_different_file(&p, &path) && !is_different_file(&path, &p)
                },
                // Note: not handle error in StdFile yet
                Err(_) => old(global_open_files).ghost_files@ =~= global_open_files.ghost_files@,
            },
    {
        let _ = global_open_files.create_checked(path)?;
        let file = StdFile::create(path).map_err(FileError::new)?;
        let ghost file_len = 0;
        let ghost content = Seq::empty();
        let virtual_file = Ghost(VirtualFile::build(file_len, content));
        Ok(VerifiedFile {
            inner: file,
            virtual_file,
        })
    }

    pub fn close(self, global_open_files: &mut GlobalOpenFiles) 
        requires
            forall |p: String| #![auto] old(global_open_files).ghost_files@.contains(p) ==> {
                !is_different_file(&p, &p) && old(global_open_files).ghost_files@.filter(|q| !is_different_file(&q, &p)).len() == 1
            }
        ensures
            old(global_open_files).ghost_files@ =~= global_open_files.ghost_files@,
            forall |p: String| #![auto] global_open_files.ghost_files@.contains(p) ==> {
                !is_different_file(&p, &p) && global_open_files.ghost_files@.filter(|q| !is_different_file(&q, &p)).len() == 1
            }, 
    {
        global_open_files.close(&self.inner);
    }

    /// Seeks to a specific position in the file
    pub fn seek(&mut self, pos: SeekFrom) -> (result: Result<u64, FileError>)
        requires
            0 <= old(self).virtual_file@.file_len <= i64::MAX as u64,
            0 <= old(self).virtual_file@.pos <= i64::MAX as u64,
        ensures
            0 <= self.virtual_file@.file_len <= i64::MAX as u64,
            0 <= self.virtual_file@.pos <= i64::MAX as u64,
            self.virtual_file@.file_len == old(self).virtual_file@.file_len,
            match result {
                Ok(n) => {
                    &&& self.virtual_file@.pos == n
                    &&& match pos {
                        SeekFrom::Start(offset) => n == offset,
                        SeekFrom::Current(offset) => n == old(self).virtual_file@.pos + offset,
                        SeekFrom::End(offset) => n == old(self).virtual_file@.file_len + offset,
                    }
                },
                Err(_) => {
                    &&& self.virtual_file@.pos == old(self).virtual_file@.pos
                    &&& match pos {
                        SeekFrom::Start(offset) => {
                            offset > i64::MAX as u64
                        },
                        SeekFrom::Current(offset) => {
                            ||| offset == i64::MIN
                            ||| offset < 0 && -offset > old(self).virtual_file@.pos
                            ||| offset > 0 && offset + old(self).virtual_file@.pos > i64::MAX as u64
                        },
                        SeekFrom::End(offset) => {
                            ||| offset == i64::MIN
                            ||| offset < 0 && -offset > old(self).virtual_file@.file_len
                            ||| offset > 0 && offset + old(self).virtual_file@.file_len > i64::MAX as u64
                        },
                    }
                },
            },
    {
        // Perform the actual seek operation
        let actual_pos = self.inner.seek(pos, Ghost(self.virtual_file@.pos), Ghost(self.virtual_file@.file_len)).map_err(FileError::new)?;
        proof {
            self.virtual_file@.pos = actual_pos as nat;
        }

        Ok(actual_pos)
    }

    /// Reads data from the file into the provided buffer
    pub fn read(&mut self, buf: &mut [u8]) -> (result: Result<usize, FileError>)
        requires
            0 <= old(self).virtual_file@.file_len <= i64::MAX as u64,
            0 <= old(self).virtual_file@.pos <= i64::MAX as u64,
        ensures
            self.virtual_file@.file_len == old(self).virtual_file@.file_len,
            0 <= self.virtual_file@.file_len <= i64::MAX as u64,
            0 <= self.virtual_file@.pos <= i64::MAX as u64,
            match result {
                Ok(bytes_read) => {
                    &&& self.virtual_file@.pos == old(self).virtual_file@.pos + bytes_read 
                    &&& buf.len() >= bytes_read
                    &&& forall |i: int| 0 <= i < bytes_read ==> self.virtual_file@.content[old(self).virtual_file@.pos + i] == buf[i]
                },
                Err(_) => self.virtual_file@.pos == old(self).virtual_file@.pos,
            },
    {
        let bytes_read = self.inner.read(buf, Ghost(self.virtual_file@.pos), Ghost(self.virtual_file@.file_len), Ghost(self.virtual_file@.content)).map_err(FileError::new)?;
        
        // Update our position based on how many bytes were read
        proof {
            self.virtual_file@.pos = self.virtual_file@.pos + bytes_read as nat;
        }
                
        Ok(bytes_read)
    }

    /// Writes data from the provided buffer to the file
    pub fn write(&mut self, buf: &[u8]) -> (result: Result<usize, FileError>)
        requires
            0 <= old(self).virtual_file@.file_len <= i64::MAX as u64,
            0 <= old(self).virtual_file@.pos <= i64::MAX as u64,
            old(self).virtual_file@.content.len() == old(self).virtual_file@.file_len,
        ensures
            0 <= self.virtual_file@.file_len <= i64::MAX as u64,
            0 <= self.virtual_file@.pos <= i64::MAX as u64,
            self.virtual_file@.content.len() == self.virtual_file@.file_len,
            match result {
                Ok(bytes_written) => {
                    &&& self.virtual_file@.pos == old(self).virtual_file@.pos + bytes_written 
                    &&& buf.len() >= bytes_written
                    &&& if self.virtual_file@.pos > old(self).virtual_file@.file_len && bytes_written > 0 {self.virtual_file@.file_len == self.virtual_file@.pos} else {self.virtual_file@.file_len == old(self).virtual_file@.file_len}
                    &&& forall |i: int| 0 <= i < bytes_written ==> self.virtual_file@.content[old(self).virtual_file@.pos + i] == buf[i]
                    &&& forall |i: int| 0 <= i < old(self).virtual_file@.file_len && !(old(self).virtual_file@.pos <= i < self.virtual_file@.pos) ==> self.virtual_file@.content[i] == old(self).virtual_file@.content[i]
                },
                Err(_) => self.virtual_file@.pos == old(self).virtual_file@.pos && self.virtual_file@.file_len == old(self).virtual_file@.file_len,
            },
    {
        let bytes_written = self.inner.write(buf, Ghost(self.virtual_file@.pos), Ghost(self.virtual_file@.file_len)).map_err(FileError::new)?;

        let ghost old_pos = self.virtual_file@.pos;
        let ghost old_file_len = self.virtual_file@.file_len;

        // Update our position based on how many bytes were written
        proof {
            self.virtual_file@.pos = old_pos + bytes_written as nat;
            assert(old_file_len == self.virtual_file@.content.len());
            if self.virtual_file@.pos > self.virtual_file@.file_len && bytes_written > 0 {
                self.virtual_file@.file_len = self.virtual_file@.pos;
            }
            let ghost append_size = (self.virtual_file@.file_len - old_file_len) as nat;
            self.virtual_file@.content = self.virtual_file@.content.add(Seq::new(append_size, |i: int| 0)); 

            assert(self.virtual_file@.content.len() == self.virtual_file@.file_len);
            assert(bytes_written == 0 || old_pos + bytes_written <= self.virtual_file@.file_len);

            if bytes_written > 0 {
                let ghost update_content = Seq::new(bytes_written as nat, |i: int| buf[i]);
                let ghost prefix = self.virtual_file@.content.take(old_pos as int);
                let ghost suffix = self.virtual_file@.content.skip(self.virtual_file@.pos as int);
                self.virtual_file@.content = prefix + update_content + suffix;
            }

            assert(bytes_written == 0 || old_pos + bytes_written <= self.virtual_file@.file_len);
            assert(self.virtual_file@.content.len() == self.virtual_file@.file_len);
            assert(forall |i: int| 0 <= i < bytes_written ==> self.virtual_file@.content[old_pos + i] == buf[i]);
        }
        
        Ok(bytes_written)
    }
// 
//     /// Gets the file length
//     pub fn len(&self) -> (result: u64)
//         ensures
//             result == self.file_len,
//     {
//         self.file_len
//     }

    // TODO: It needs a mutable reference to self to update the file_len now. We can fix it later.
    // /// Sets the file length
    // pub fn set_len(&self, size: u64) -> (result: Result<(), FileError>)
    // {
    //     self.file_len = size;
    //     self.inner.set_len(size).map_err(FileError::new)
    // }

    /// Synchronizes all data to the file system
    pub fn sync_all(&self) -> (result: Result<(), FileError>)
    {
        self.inner.sync_all().map_err(FileError::new)
    }
}

}