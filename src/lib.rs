//! Parser for the PalmDB format
//!
//! This was created using a spec at the MobileRead wiki here:
//! [https://wiki.mobileread.com/...](https://wiki.mobileread.com/wiki/PDB#Palm_Database_Format),
//! as well as from the Calibre implementation here:
//! [https://github.com/kovidgoyal/calibre/...][1]
//!
//! [1]: https://github.com/kovidgoyal/calibre/blob/e333001d31dc49102fe5178bd2a8af4f06962fac/src/calibre/ebooks/pdb/header.py
//!
//! # Example
//!
//! ```rust,ignore
//! extern crate palmdb;
//! use palmdb::PalmDB;
//! use std::fs::File;
//! use std::io::Read;
//! # fn main() {
//! #   if let Err(_) = run() {
//! #       ::std::process::exit(1);
//! #   }
//! # }
//! # fn run() -> Result<(), ::std::io::Error> {
//!
//! let mut db_file = File::open("/path/to/some/palmdb/file")?;
//! let mut input = vec![];
//! db_file.read_to_end(&mut input)?;
//! let db = PalmDB::parse(&input).expect("Couldn't parse DB");
//!
//! #   Ok(())
//! # }
//! ```
#![deny(missing_docs,
        missing_debug_implementations, missing_copy_implementations,
        trivial_casts,
        // trivial_numeric_casts, // <- something in the `named!` macro is tripping this,
                                  // so disabling it for now
        unsafe_code,
        unstable_features,
        unused_import_braces, unused_qualifications)]


#[macro_use]
extern crate nom;
#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate bitflags;

use std::str;
use std::fmt;

use nom::{rest, IResult, be_u16, be_u32, be_u8};

pub use errors::*;

#[allow(unused_doc_comment)]
mod errors {
    error_chain!{}
}

/// Represents a parsed PalmDB
///
/// Records in the DB can be accessed using the `.get` method
///
/// # Example
///
/// ```rust,ignore
/// extern crate palmdb;
/// use std::fs::File;
/// use std::io::Read;
/// use palmdb::PalmDB;
///
/// # fn main() {
/// #   if let Err(_) = run() {
/// #     ::std::process::exit(1);
/// #   }
/// # fn run() -> Result<(), Box<Error>> {
///
/// let mut db_file = File::open("/path/to/some/palmdb/file")?;
/// let mut input = vec![];
/// db_file.read_to_end(&mut input);
/// let db = PalmDB::parse(&input);
/// let first_record = db.get(0);
/// #   Ok(())
/// # }
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq)]
pub struct PalmDB<'a> {
    pub name: &'a str,
    attributes: Attributes,
    pub version: u16,
    /// should represent the number of seconds since the unix epoch,
    /// but see the note here: https://wiki.mobileread.com/wiki/PDB#PDB_Times
    pub creation_date: u32,
    /// should represent the number of seconds since the unix epoch,
    /// but see the note here: https://wiki.mobileread.com/wiki/PDB#PDB_Times
    pub modified_date: u32,
    /// should represent the number of seconds since the unix epoch,
    /// but see the note here: https://wiki.mobileread.com/wiki/PDB#PDB_Times
    pub last_backup_date: u32,
    pub modification_number: u32,
    pub app_info_id: u32,
    pub sort_info_id: u32,
    /// `type_` and `creator`, together, represent the values in
    /// this table: https://wiki.mobileread.com/wiki/PDB#Palm_Database_File_Code
    pub type_: &'a str,
    /// `type_` and `creator`, together, represent the values in
    /// this table: https://wiki.mobileread.com/wiki/PDB#Palm_Database_File_Code
    pub creator: &'a str,
    pub unique_id_seed: u32,
    pub next_record_list_id: u32,
    num_records: u16,
    record_info_list: &'a [u8],
    records: &'a [u8],
}

impl<'a> PalmDB<'a> {
    /// Takes a byte slice as input and attempts to parse it into a `PalmDB` structure
    pub fn parse(input: &'a [u8]) -> Result<PalmDB<'a>> {
        match parse_db(&input) {
            IResult::Done(_, o) => {
                Ok(o)
            },
            _ => {
                Err(ErrorKind::Msg("Could not parse PalmDB file".into()).into())
            }
        }
    }

    /// Returns the metadata for record `number`. If there is no record at that index,
    /// returns an `Err`
    pub fn record_info(&self, number: usize) -> Result<RecordInfo> {
        if number >= self.num_records as usize {
            return Err(
                ErrorKind::Msg(format!("Record number {} is out-of-bounds", number)).into(),
            );
        }
        let start = number * 8;
        let end = start + 8;
        let parsed = record_info_parser(&self.record_info_list[start..end]);
        Ok(match parsed {
            IResult::Done(_, o) => {
                let (offset, attrs, a1, a2, a3) = o;
                RecordInfo {
                    offset,
                    attrs,
                    val: (a1 as u32) << 16 | (a2 as u32) << 8 | (a3 as u32),
                }
            }
            _ => {
                return Err(
                    ErrorKind::Msg(format!("Could not parse record info")).into(),
                )
            }
        })
    }

    fn offset_to_idx(&self, offset: usize) -> Result<usize> {
        // the offset from the record info gives us the offset within the entire file, and
        // we need to convert that to an index into the `records` buffer

        // so, get how many bytes it is to the first record in the file
        let base = self.record_info(0)?;

        // the `offset` parameter is the offset into the file of the record we want

        // subtract the two, and we should get the index into the records buffer that we need
        Ok(offset - base.offset as usize)
    }

    fn is_last(&self, number: usize) -> bool {
        number == (self.num_records - 1) as usize
    }

    /// Retreives record `number` from the database. If the
    /// record number does not exist, returns an `Err`
    pub fn get(&self, number: usize) -> Result<&'a [u8]> {
        let record_info = self.record_info(number)?;
        let loc = record_info.offset;

        let start = self.offset_to_idx(loc as usize)?;

        let end = if self.is_last(number) {
            self.records.len()
        } else {
            let next_record = self.record_info(number + 1)?;
            let next_offset = next_record.offset;
            self.offset_to_idx(next_offset as usize)?
        };
        Ok(&self.records[start..end])
    }

    /// Returns true if the `0x0002` bit is set for the DB
    pub fn is_read_only(&self) -> bool {
        self.attributes.contains(READ_ONLY)
    }

    /// Returns true if the `0x0004` bit is set for the DB
    pub fn app_info_area_is_dirty(&self) -> bool {
        self.attributes.contains(DIRTY_APP_INFO_AREA)
    }

    /// Returns true if the `0x0008` bit is set for the DB
    pub fn do_backup(&self) -> bool {
        self.attributes.contains(BACKUP)
    }

    /// Returns true if the `0x0010` bit is set for the DB
    pub fn okay_to_install_over(&self) -> bool {
        self.attributes.contains(INSTALL_OVER)
    }

    /// Returns true if the `0x0020` bit is set for the DB
    pub fn do_force_reset(&self) -> bool {
        self.attributes.contains(FORCE_RESET)
    }

    /// Returns true if the `0x0040` bit is set for the DB
    pub fn no_allow_copy(&self) -> bool {
        self.attributes.contains(NO_ALLOW_COPY)
    }

    /// Returns the number of records in the DB
    pub fn len(&self) -> usize {
        self.num_records as usize
    }
}

impl<'a> fmt::Display for PalmDB<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "PalmDB {{
    name: {},
    attributes: {:?},
    version: {},
    creation_date: {},
    modified_date: {},
    last_backup_date: {},
    modification_number: {},
    app_info_id: {},
    sort_info_id: {},
    type_: {},
    creator: {},
    unique_id_seed: {},
    next_record_list_id: {},
    num_records: {},
    record_info_list: <{} bytes>,
    records: <{} bytes>,
}}",
            self.name,
            self.attributes,
            self.version,
            self.creation_date,
            self.modified_date,
            self.last_backup_date,
            self.modification_number,
            self.app_info_id,
            self.sort_info_id,
            self.type_,
            self.creator,
            self.unique_id_seed,
            self.next_record_list_id,
            self.num_records,
            self.record_info_list.len(),
            self.records.len()
        )
    }
}

/// Metadata for a specific record
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecordInfo {
    /// Indicates the offset *from the beginning of the file*.
    /// It should not be used as an index into the `PalmDB::records`
    /// field
    pub offset: u32,
    attrs: RecordAttributes,
    val: u32,
}

impl RecordInfo {
    /// Returns true if the `0x10` bit is set for the record
    pub fn is_secret(&self) -> bool {
        self.attrs.contains(SECRET_RECORD_BIT)
    }

    /// Returns true if the `0x20` bit is set for the record
    pub fn is_in_use(&self) -> bool {
        self.attrs.contains(BUSY_BIT)
    }

    /// Returns true if the `0x40` bit is set for the record
    pub fn is_dirty(&self) -> bool {
        self.attrs.contains(DIRTY_RECORD_BIT)
    }

    /// Returns true if the `0x80` bit is set for the record
    pub fn delete_on_next_hotsync(&self) -> bool {
        self.attrs.contains(DELETE_ON_NEXT_HOTSYNC)
    }
}

bitflags! {
    struct Attributes: u32 {
        const READ_ONLY =           0b0000_0010;
        const DIRTY_APP_INFO_AREA = 0b0000_0100;
        const BACKUP =              0b0000_1000;
        const INSTALL_OVER =        0b0001_0000;
        const FORCE_RESET =         0b0010_0000;
        const NO_ALLOW_COPY =       0b0100_0000;
    }
}

bitflags! {
    struct RecordAttributes: u32 {
        const SECRET_RECORD_BIT =       0b0001_0000;
        const BUSY_BIT =                0b0010_0000;
        const DIRTY_RECORD_BIT =        0b0100_0000;
        const DELETE_ON_NEXT_HOTSYNC =  0b1000_0000;
    }
}

named!(record_info_parser< (u32, RecordAttributes, u8, u8, u8) >,
    do_parse!(
        offset: be_u32 >>
        attrs: map_opt!(be_u8, |a| RecordAttributes::from_bits(a as u32)) >>
        a1: be_u8 >>
        a2: be_u8 >>
        a3: be_u8 >>
        ((offset, attrs, a1, a2, a3))
    )
);

named!(parse_db< PalmDB >,
    do_parse!(
        name: map!(map_res!(take!(31), str::from_utf8), |s| s.trim_matches('\0')) >>
        tag!(b"\0") >>
        attributes: map_opt!(be_u16, |a| Attributes::from_bits(a as u32)) >>
        version: be_u16 >>
        creation_date: be_u32 >>
        modified_date: be_u32 >>
        last_backup_date: be_u32 >>
        modification_number: be_u32 >>
        app_info_id: be_u32 >>
        sort_info_id: be_u32 >>
        type_: map_res!(take!(4), str::from_utf8) >>
        creator: map_res!(take!(4), str::from_utf8) >>
        unique_id_seed: be_u32 >>
        next_record_list_id: be_u32 >>
        num_records: be_u16 >>
        record_info_list: take!(8 * num_records) >>
        opt!(tag!("\u{0}\u{0}")) >>
        records: rest >>
        (PalmDB {
            name: name,
            attributes: attributes,
            version: version,
            creation_date,
            modified_date,
            last_backup_date,
            modification_number,
            app_info_id,
            sort_info_id,
            type_,
            creator,
            unique_id_seed,
            next_record_list_id,
            num_records,
            record_info_list,
            records,
        })
    )
);

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::Read;
    use std::str;

    use nom::IResult;

    #[test]
    fn test_record_info_parser() {}

    #[test]
    fn test_parse_db() {}
}
