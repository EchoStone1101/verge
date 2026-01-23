use vstd::prelude::*;
use std::path::{Path, PathBuf};
use std::io::{Seek, SeekFrom, Read, Write};
use std::ffi::OsString;
use std::sync::Arc;
use std::os::unix::fs::{OpenOptionsExt, MetadataExt};
use std::os::fd::AsRawFd;
use std::marker::PointeeSized;

verus! {

#[verifier::external_trait_specification]
pub trait ExAsRef<T: PointeeSized>: PointeeSized {
    type ExternalTraitSpecificationFor: AsRef<T>;

    fn as_ref(&self) -> &T;
}

#[verifier::external_trait_specification]
pub trait ExAsRawFd {
    type ExternalTraitSpecificationFor: AsRawFd;

    fn as_raw_fd(&self) -> i32;
}

#[verifier::external_type_specification]
pub struct ExSeekFrom(std::io::SeekFrom);

#[verifier::external_body]
pub struct IoError(std::io::Error);

#[verifier::external_body]
pub struct StdFile(std::fs::File);

uninterp spec fn get_file_len<P: AsRef<Path>>(path: P) -> nat;

impl StdFile {
    #[verifier::external_body]
    pub fn open<P: AsRef<Path>>(path: P) -> (result: Result<(StdFile, Ghost<nat>), IoError>)
        ensures
            match result {
                Result::Ok((_, file_len)) => 0 <= file_len@ <= i64::MAX,
                Result::Err(_) => true,
            },
    {
        let std_file = std::fs::File::open(path).map_err(IoError)?;
        let ghost file_len = get_file_len(path);
        Ok((StdFile(std_file), Ghost(file_len)))
    }

    #[verifier::external_body]
    pub fn create<P: AsRef<Path>>(path: P) -> Result<StdFile, IoError> {
        let std_file = std::fs::File::create(path).map_err(IoError)?;
        Ok(StdFile(std_file))
    }

    #[verifier::external_body]
    pub fn create_new<P: AsRef<Path>>(path: P) -> Result<StdFile, IoError> {
        let std_file = std::fs::File::create_new(path).map_err(IoError)?;
        Ok(StdFile(std_file))
    }

    #[verifier::external_body]
    pub fn options() -> StdOpenOptions {
        StdOpenOptions::new()
    }

    #[verifier::external_body]
    pub fn sync_all(&self) -> Result<(), IoError> {
        self.0.sync_all().map_err(IoError)
    }

    #[verifier::external_body]
    pub fn sync_data(&self) -> Result<(), IoError> {
        self.0.sync_data().map_err(IoError)
    }

    #[verifier::external_body]
    pub fn set_len(&self, size: u64) -> Result<(), IoError> {
        self.0.set_len(size).map_err(IoError)
    }

    #[verifier::external_body]
    pub fn metadata(&self) -> Result<StdMetadata, IoError> {
        self.0.metadata().map(|m| StdMetadata(m)).map_err(IoError)
    }

    #[verifier::external_body]
    pub fn try_clone(&self) -> Result<StdFile, IoError> {
        let std_file = self.0.try_clone().map_err(IoError)?;
        Ok(StdFile(std_file))
    }

    #[verifier::external_body]
    pub fn set_permissions(&self, perm: StdPermissions) -> Result<(), IoError> {
        self.0.set_permissions(perm.0).map_err(IoError)
    }

//     #[verifier::external_body]
//     pub fn set_modified(&self, time: std::time::SystemTime) -> Result<(), IoError> {
//         self.0.set_modified(time).map_err(IoError)
//     }

    #[verifier::external_body]
    pub fn read(&mut self, buf: &mut [u8], cur_pos: Ghost<nat>, file_len: Ghost<nat>, content: Ghost<Seq<u8>>) -> (result: Result<usize, IoError>) 
        requires
            0 <= cur_pos@ <= i64::MAX,
            0 <= file_len@ <= i64::MAX,
        ensures
            match result {
                Result::Ok(n) => {
                    &&& 0 <= n <= buf.len() 
                    &&& if cur_pos@ < file_len@ { n <= file_len@ - cur_pos@ } else { n == 0 }
                    &&& forall|i: int| 0 <= i < n ==> buf[i] == content@[cur_pos@ + i]
                },
                Result::Err(_) => true,
            },
    {
        self.0.read(buf).map_err(IoError)
    }

    #[verifier::external_body]
    pub fn read_to_end(&mut self, buf: &mut Vec<u8>) -> Result<usize, IoError> {
        self.0.read_to_end(buf).map_err(IoError)
    }

    #[verifier::external_body]
    pub fn write(&mut self, buf: &[u8], cur_pos: Ghost<nat>, file_len: Ghost<nat>) -> (result: Result<usize, IoError>) 
        requires
            0 <= cur_pos@ <= i64::MAX,
            0 <= file_len@ <= i64::MAX,
        ensures
            match result {
                Result::Ok(n) => {
                    &&& 0 <= n <= buf.len() 
                    &&& n <= i64::MAX
                    &&& cur_pos@ + n <= i64::MAX
                },
                Result::Err(_) => true,
            },
    {
        self.0.write(buf).map_err(IoError)
    }

    #[verifier::external_body]
    pub fn clone(&self) -> StdFile {
        StdFile(self.0.try_clone().unwrap())
    }

    #[verifier::external_body]
    pub fn seek(&mut self, pos: SeekFrom, cur_pos: Ghost<nat>, file_len: Ghost<nat>) -> (result: Result<u64, IoError>) 
        ensures
            match result {
                Ok(n) => {
                    &&& 0 <= n <= i64::MAX as u64
                    &&& match pos {
                        SeekFrom::Start(offset) => n == offset,
                        SeekFrom::Current(offset) => n == cur_pos@ + offset,
                        SeekFrom::End(offset) => n == file_len@ + offset,
                    }
                },
                Err(_) => {
                    match pos {
                        SeekFrom::Start(offset) => {
                            offset > i64::MAX as u64
                        },
                        SeekFrom::Current(offset) => {
                            ||| offset == i64::MIN
                            ||| offset < 0 && -offset > cur_pos@
                            ||| offset > 0 && offset + cur_pos@ > i64::MAX as u64
                        },
                        SeekFrom::End(offset) => {
                            ||| offset == i64::MIN
                            ||| offset < 0 && -offset > file_len@
                            ||| offset > 0 && offset + file_len@ > i64::MAX as u64
                        },
                    }
                },
            },
    {
        self.0.seek(pos).map_err(IoError)
    }
}

impl AsRawFd for StdFile {
    #[verifier::external_body]
    fn as_raw_fd(&self) -> i32 {
        self.0.as_raw_fd()
    }
}

#[verifier::external_body]
pub struct StdOpenOptions(std::fs::OpenOptions);

impl StdOpenOptions {
    #[verifier::external_body]
    pub fn new() -> StdOpenOptions {
        StdOpenOptions(std::fs::OpenOptions::new())
    }
    #[verifier::external_body]
    pub fn read(&mut self, read: bool) {
        self.0.read(read);
    }
    #[verifier::external_body]
    pub fn write(&mut self, write: bool) {
        self.0.write(write);
    }
    #[verifier::external_body]
    pub fn append(&mut self, append: bool) {
        self.0.append(append);
    }
    #[verifier::external_body]
    pub fn truncate(&mut self, truncate: bool) {
        self.0.truncate(truncate);
    }
    #[verifier::external_body]
    pub fn create(&mut self, create: bool) {
        self.0.create(create);
    }
    #[verifier::external_body]
    pub fn create_new(&mut self, create_new: bool) {
        self.0.create_new(create_new);
    }
    #[verifier::external_body]
    pub fn custom_flags(&mut self, flags: i32) {
        self.0.custom_flags(flags);
    }
    #[verifier::external_body]
    pub fn open<P: AsRef<Path>>(&self, path: P) -> Result<StdFile, IoError> {
        let std_file = self.0.open(path).map_err(IoError)?;
        Ok(StdFile(std_file))
    }
}

#[verifier::external_body]
pub struct StdMetadata(std::fs::Metadata);

impl StdMetadata {
    #[verifier::external_body]
    pub fn file_type(&self) -> StdFileType {
        StdFileType(self.0.file_type())
    }

    #[verifier::external_body]
    pub fn is_dir(&self) -> bool {
        self.0.is_dir()
    }

    #[verifier::external_body]
    pub fn is_file(&self) -> bool {
        self.0.is_file()
    }

    #[verifier::external_body]
    pub fn is_symlink(&self) -> bool {
        self.0.is_symlink()
    }

    #[verifier::external_body]
    pub fn len(&self) -> (len: u64) 
        ensures
            len >= 0,
    {
        self.0.len()
    }

    #[verifier::external_body]
    pub fn dev(&self) -> u64 {
        self.0.dev()
    }

    #[verifier::external_body]
    pub fn ino(&self) -> u64 {
        self.0.ino()
    }

    #[verifier::external_body]
    pub fn permissions(&self) -> StdPermissions {
        StdPermissions(self.0.permissions())
    }

//     #[verifier::external_body]
//     pub fn modified(&self) -> Result<std::time::SystemTime, IoError> {
//         self.0.modified().map_err(IoError)
//     }
// 
//     #[verifier::external_body]
//     pub fn accessed(&self) -> Result<std::time::SystemTime, IoError> {
//         self.0.accessed().map_err(IoError)
//     }
// 
//     #[verifier::external_body]
//     pub fn created(&self) -> Result<std::time::SystemTime, IoError> {
//         self.0.created().map_err(IoError)
//     }
}

#[verifier::external_body]
pub struct StdFileType(std::fs::FileType);

impl StdFileType {
    #[verifier::external_body]
    pub fn is_dir(&self) -> bool {
        self.0.is_dir()
    }

    #[verifier::external_body]
    pub fn is_file(&self) -> bool {
        self.0.is_file()
    }

    #[verifier::external_body]
    pub fn is_symlink(&self) -> bool {
        self.0.is_symlink()
    }
}

#[verifier::external_body]
pub struct StdPermissions(std::fs::Permissions);

impl StdPermissions {
    #[verifier::external_body]
    pub fn readonly(&self) -> bool {
        self.0.readonly()
    }

    #[verifier::external_body]
    pub fn set_readonly(&mut self, readonly: bool) {
        self.0.set_readonly(readonly)
    }
}

#[verifier::external_body]
pub struct StdReadDir(std::fs::ReadDir);

// impl Iterator for StdReadDir {
//     type Item = Result<DirEntry, IoError>;
// 
//     #[verifier::external_body]
//     fn next(&mut self) -> Option<Self::Item> {
//         self.0.next().map(|result| result.map(|entry| DirEntry(entry)).map_err(IoError))
//     }
// }

#[verifier::external_body]
pub struct StdPathBuf(std::path::PathBuf);

#[verifier::external_body]
pub struct StdOsString(std::ffi::OsString);

#[verifier::external_body]
pub struct StdDirEntry(std::fs::DirEntry);

impl StdDirEntry {
    #[verifier::external_body]
    pub fn path(&self) -> StdPathBuf {
        StdPathBuf(self.0.path())
    }

    #[verifier::external_body]
    pub fn metadata(&self) -> Result<StdMetadata, IoError> {
        self.0.metadata().map(|m| StdMetadata(m)).map_err(IoError)
    }

    #[verifier::external_body]
    pub fn file_type(&self) -> Result<StdFileType, IoError> {
        self.0.file_type().map(|t| StdFileType(t)).map_err(IoError)
    }

    #[verifier::external_body]
    pub fn file_name(&self) -> StdOsString {
        StdOsString(self.0.file_name())
    }
}

// #[verifier::external_body]
// pub struct DirBuilder {
//     inner: std::fs::DirBuilder,
//     recursive: bool,
// }
// 
// impl DirBuilder {
//     #[verifier::external_body]
//     pub fn new() -> DirBuilder {
//         DirBuilder { inner: std::fs::DirBuilder::new(), recursive: false }
//     }
// 
//     #[verifier::external_body]
//     pub fn recursive(&mut self, recursive: bool) -> &mut Self {
//         self.recursive = recursive;
//         self
//     }
// 
//     #[verifier::external_body]
//     pub fn create<P: AsRef<Path>>(&self, path: P) -> Result<(), IoError> {
//         if self.recursive {
//             std::fs::create_dir_all(path).map_err(IoError)
//         } else {
//             self.inner.create(path).map_err(IoError)
//         }
//     }
// }

#[verifier::external_body]
pub fn read<P: AsRef<Path>>(path: P) -> Result<Vec<u8>, IoError> {
    std::fs::read(path).map_err(IoError)
}

#[verifier::external_body]
pub fn read_to_string<P: AsRef<Path>>(path: P) -> Result<String, IoError> {
    std::fs::read_to_string(path).map_err(IoError)
}

#[verifier::external_body]
pub fn write<P: AsRef<Path>, C: AsRef<[u8]>>(path: P, contents: C) -> Result<(), IoError> {
    std::fs::write(path, contents).map_err(IoError)
}

#[verifier::external_body]
pub fn remove_file<P: AsRef<Path>>(path: P) -> Result<(), IoError> {
    std::fs::remove_file(path).map_err(IoError)
}

#[verifier::external_body]
pub fn metadata<P: AsRef<Path>>(path: P) -> Result<StdMetadata, IoError> {
    std::fs::metadata(path).map(|m| StdMetadata(m)).map_err(IoError)
}

#[verifier::external_body]
pub fn symlink_metadata<P: AsRef<Path>>(path: P) -> Result<StdMetadata, IoError> {
    std::fs::symlink_metadata(path).map(|m| StdMetadata(m)).map_err(IoError)
}

#[verifier::external_body]
pub fn rename<P: AsRef<Path>, Q: AsRef<Path>>(from: P, to: Q) -> Result<(), IoError> {
    std::fs::rename(from, to).map_err(IoError)
}

#[verifier::external_body]
pub fn copy<P: AsRef<Path>, Q: AsRef<Path>>(from: P, to: Q) -> Result<u64, IoError> {
    std::fs::copy(from, to).map_err(IoError)
}

#[verifier::external_body]
pub fn hard_link<P: AsRef<Path>, Q: AsRef<Path>>(original: P, link: Q) -> Result<(), IoError> {
    std::fs::hard_link(original, link).map_err(IoError)
}

#[verifier::external_body]
pub fn read_link<P: AsRef<Path>>(path: P) -> Result<StdPathBuf, IoError> {
    std::fs::read_link(path).map(|p| StdPathBuf(p)).map_err(IoError)
}

#[verifier::external_body]
pub fn canonicalize<P: AsRef<Path>>(path: P) -> Result<StdPathBuf, IoError> {
    std::fs::canonicalize(path).map(|p| StdPathBuf(p)).map_err(IoError)
}

#[verifier::external_body]
pub fn create_dir<P: AsRef<Path>>(path: P) -> Result<(), IoError> {
    std::fs::create_dir(path).map_err(IoError)
}

#[verifier::external_body]
pub fn create_dir_all<P: AsRef<Path>>(path: P) -> Result<(), IoError> {
    std::fs::create_dir_all(path).map_err(IoError)
}

#[verifier::external_body]
pub fn remove_dir<P: AsRef<Path>>(path: P) -> Result<(), IoError> {
    std::fs::remove_dir(path).map_err(IoError)
}

#[verifier::external_body]
pub fn remove_dir_all<P: AsRef<Path>>(path: P) -> Result<(), IoError> {
    std::fs::remove_dir_all(path).map_err(IoError)
}

#[verifier::external_body]
pub fn read_dir<P: AsRef<Path>>(path: P) -> Result<StdReadDir, IoError> {
    std::fs::read_dir(path).map(|rd| StdReadDir(rd)).map_err(IoError)
}

#[verifier::external_body]
pub fn set_permissions<P: AsRef<Path>>(path: P, perm: StdPermissions) -> Result<(), IoError> {
    std::fs::set_permissions(path, perm.0).map_err(IoError)
}

#[verifier::external_body]
pub fn file_exists<P: AsRef<Path>>(path: P) -> Result<bool, IoError> {
    std::fs::exists(path).map_err(IoError)
}

}