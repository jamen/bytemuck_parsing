use bytemuck::{AnyBitPattern, PodCastError};
use core::mem::size_of;

/// Removes and returns items from the beginning of a slice.
///
/// The `slice_take` feature on nightly should replace this eventually (see [issue 62280](https://github.com/rust-lang/rust/issues/62280))
///
/// # Examples
///
/// ```rust
/// use bytemuck_parsing::take;
///
/// let mut i = b"Hello world".as_slice();
/// let o = take(&mut i, 5);
/// assert_eq!(o, Some(b"Hello".as_slice()));
/// assert_eq!(i, b" world".as_slice());
/// ```
pub fn take<'a, T>(input: &mut &'a [T], n: usize) -> Option<&'a [T]> {
    if n > input.len() {
        return None;
    }
    let (front, back) = input.split_at(n);
    *input = back;
    Some(front)
}

/// Parses the beginning of the input as a plain-old-data type, removing and returning it. See [`bytemuck::Pod`] for more details on plain-old-data types.
///
/// ```rust
/// use bytemuck_parsing::parse;
///
/// let mut i: &[u8] = &[ 1, 0, 0, 0, 2, 2, 2, 2 ];
/// let o = parse::<u32>(&mut i);
/// assert_eq!(o, Ok(1));
/// assert_eq!(i, [ 2, 2, 2, 2 ]);
/// ```
pub fn parse<T: AnyBitPattern>(input: &mut &[u8]) -> Result<T, PodCastError> {
    let bytes = take(input, size_of::<T>()).ok_or(PodCastError::SizeMismatch)?;
    Ok(bytemuck::try_pod_read_unaligned(bytes)?)
}

macro_rules! impl_int_parsers {
    ($($(#[$fn_meta:meta])* $fn_vis:vis fn $fn_name:ident { $int_type:ty, $to_endian_fn:ident });* $(;)?) => {
        $(
            $(#[$fn_meta])*
            $fn_vis fn $fn_name(input: &mut &[u8]) -> Result<$int_type, PodCastError> {
                Ok($crate::parse::<$int_type>(input)?.$to_endian_fn())
            }
        )*
    };
}

impl_int_parsers! {
    // Unsigned little-endian

    /// Parse bytes from the beginning of a slice as an unsigned 16-bit little-endian integer.
    pub fn parse_u16_le { u16, to_le };

    /// Parse bytes from the beginning of a slice as an unsigned 32-bit little-endian integer.
    pub fn parse_u32_le { u32, to_le };

    /// Parse bytes from the beginning of a slice as an unsigned 64-bit little-endian integer.
    pub fn parse_u64_le { u64, to_le };

    /// Parse bytes from the beginning of a slice as an unsigned 128-bit little-endian integer.
    pub fn parse_u128_le { u128, to_le };

    // Unsigned big-endian

    /// Parse bytes from the beginning of a slice as an unsigned 16-bit big-endian integer.
    pub fn parse_u16_be { u16, to_be };

    /// Parse bytes from the beginning of a slice as an unsigned 32-bit big-endian integer.
    pub fn parse_u32_be { u32, to_be };

    /// Parse bytes from the beginning of a slice as an unsigned 64-bit big-endian integer.
    pub fn parse_u64_be { u64, to_be };

    /// Parse bytes from the beginning of a slice as an unsigned 128-bit big-endian integer.
    pub fn parse_u128_be { u128, to_be };

    // Signed little-endian

    /// Parse bytes from the beginning of a slice as a signed 16-bit little-endian integer.
    pub fn parse_i16_le { i16, to_le };

    /// Parse bytes from the beginning of a slice as a signed 32-bit little-endian integer.
    pub fn parse_i32_le { i32, to_le };

    /// Parse bytes from the beginning of a slice as a signed 64-bit little-endian integer.
    pub fn parse_i64_le { i64, to_le };

    /// Parse bytes from the beginning of a slice as a signed 128-bit little-endian integer.
    pub fn parse_i128_le { i128, to_le };

    // Signed big-endian

    /// Parse bytes from the beginning of a slice as a signed 16-bit big-endian integer.
    pub fn parse_i16_be { i16, to_be };

    /// Parse bytes from the beginning of a slice as a signed 32-bit big-endian integer.
    pub fn parse_i32_be { i32, to_be };

    /// Parse bytes from the beginning of a slice as a signed 64-bit big-endian integer.
    pub fn parse_i64_be { i64, to_be };

    /// Parse bytes from the beginning of a slice as a signed 128-bit big-endian integer.
    pub fn parse_i128_be { i128, to_be };
}
