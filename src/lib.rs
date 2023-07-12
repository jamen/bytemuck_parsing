#![no_std]

use bytemuck::{AnyBitPattern, PodCastError};
use core::str::Utf8Error;
use core::{marker::PhantomData, mem::size_of};
use derive_more::{Display, From};

#[derive(Debug, Display, PartialEq, Eq, Copy, Clone)]
#[display(fmt = "input ended unexpectedly")]
pub struct InputEndedError;

/// Removes and returns items from the beginning of a slice.
///
/// The `slice_take` feature on nightly should replace this eventually
/// (see [issue 62280](https://github.com/rust-lang/rust/issues/62280)).
///
/// # Examples
///
/// ```rust
/// use bytemuck_parsing::take;
///
/// let mut i = b"Hello world".as_slice();
/// let o = take(&mut i, 5);
/// assert_eq!(o, Ok(b"Hello".as_slice()));
/// assert_eq!(i, b" world".as_slice());
/// ```
pub fn take<'a, T>(input: &mut &'a [T], n: usize) -> Result<&'a [T], InputEndedError> {
    if n > input.len() {
        return Err(InputEndedError);
    }
    let (front, back) = input.split_at(n);
    *input = back;
    Ok(front)
}

#[derive(Display, Debug, From, Copy, Clone, PartialEq, Eq)]
pub enum TakeStrWithLenError {
    InputEnded(InputEndedError),
    Utf8(Utf8Error),
}

/// Removes and returns a UTF-8 string from the beginning of a byte slice.
///
/// ```rust
/// use bytemuck_parsing::take_str_with_len;
///
/// let mut i = b"Hello world".as_slice();
/// let o = take_str_with_len(&mut i, 5);
/// assert_eq!(o, Ok("Hello"));
/// assert_eq!(i, b" world".as_slice());
/// ```
pub fn take_str_with_len<'a>(
    input: &mut &'a [u8],
    len: usize,
) -> Result<&'a str, TakeStrWithLenError> {
    let bytes = take(input, len)?;
    let string = core::str::from_utf8(bytes)?;
    Ok(string)
}

#[derive(Display, Debug, From, Copy, Clone, PartialEq, Eq)]
pub enum ParseError {
    InputEnded(InputEndedError),
    PodCast(PodCastError),
}

impl<T> From<ParseIntError<T>> for ParseError {
    fn from(x: ParseIntError<T>) -> Self {
        x.into_inner()
    }
}

impl<T> From<ParseFloatError<T>> for ParseError {
    fn from(x: ParseFloatError<T>) -> Self {
        x.into_inner()
    }
}

/// Parse a plain-old-data type. See [`bytemuck::Pod`] for more details.
///
/// # Examples
///
/// Parsing an array
///
/// ```rust
/// use bytemuck_parsing::parse;
///
/// let mut i: &[u8] = &[1, 0, 0, 0, 2, 2, 2, 2];
/// let o = parse::<[u8; 4]>(&mut i);
/// assert_eq!(o, Ok([1, 0, 0, 0]));
/// assert_eq!(i, [2, 2, 2, 2]);
/// ```
pub fn parse<T: AnyBitPattern>(input: &mut &[u8]) -> Result<T, ParseError> {
    let bytes = take(input, size_of::<T>())?;
    let data_type = bytemuck::try_pod_read_unaligned(bytes)?;
    Ok(data_type)
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct ParseIntError<T>(ParseError, PhantomData<T>);

impl<T> ParseIntError<T> {
    pub fn into_inner(self) -> ParseError {
        self.0
    }
}

impl<T> From<ParseError> for ParseIntError<T> {
    fn from(x: ParseError) -> Self {
        Self(x, Default::default())
    }
}

impl<T> core::fmt::Display for ParseIntError<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

macro_rules! impl_int_parsers {
    (
        $(
            $(#[$fn_meta:meta])*
            $fn_vis:vis fn $fn_name:ident { $int_type:ty, $to_endian_fn:ident }
        );* $(;)?
    ) => {
        $(
            $(#[$fn_meta])*
            $fn_vis fn $fn_name(input: &mut &[u8]) -> Result<$int_type, ParseIntError<$int_type>> {
                let raw_int = $crate::parse::<$int_type>(input)?;
                let specified_endianness_int = raw_int.$to_endian_fn();
                Ok(specified_endianness_int)
            }
        )*
    };
}

impl_int_parsers! {
    // Unsigned little-endian integers

    /// Parse an unsigned 16-bit little-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_u16_le;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0x03, 0x7];
    /// let o = parse_u16_le(&mut i);
    /// assert_eq!(o, Ok(0xFFFE));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_u16_le { u16, to_le };

    /// Parse an unsigned 32-bit little-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_u32_le;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0xFF, 0xFF, 0x03, 0x7];
    /// let o = parse_u32_le(&mut i);
    /// assert_eq!(o, Ok(0xFFFFFFFE));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_u32_le { u32, to_le };

    /// Parse an unsigned 64-bit little-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_u64_le;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x7];
    /// let o = parse_u64_le(&mut i);
    /// assert_eq!(o, Ok(0xFFFFFFFFFFFFFFFE));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_u64_le { u64, to_le };

    /// Parse an unsigned 128-bit little-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_u128_le;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    /// 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x7];
    /// let o = parse_u128_le(&mut i);
    /// assert_eq!(o, Ok(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_u128_le { u128, to_le };

    // Unsigned big-endian integers

    /// Parse an unsigned 16-bit big-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_u16_be;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0x03, 0x7];
    /// let o = parse_u16_be(&mut i);
    /// assert_eq!(o, Ok(0xFEFF));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_u16_be { u16, to_be };

    /// Parse an unsigned 32-bit big-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_u32_be;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0xFF, 0xFF, 0x03, 0x7];
    /// let o = parse_u32_be(&mut i);
    /// assert_eq!(o, Ok(0xFEFFFFFF));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_u32_be { u32, to_be };

    /// Parse an unsigned 64-bit big-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_u64_be;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x7];
    /// let o = parse_u64_be(&mut i);
    /// assert_eq!(o, Ok(0xFEFFFFFFFFFFFFFF));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_u64_be { u64, to_be };

    /// Parse an unsigned 128-bit big-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_u128_be;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    /// 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x7];
    /// let o = parse_u128_be(&mut i);
    /// assert_eq!(o, Ok(0xFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_u128_be { u128, to_be };

    // Signed little-endian integers

    /// Parse a signed 16-bit little-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_i16_le;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0x03, 0x7];
    /// let o = parse_i16_le(&mut i);
    /// assert_eq!(o, Ok(0xFFFEu16 as i16));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_i16_le { i16, to_le };

    /// Parse a signed 32-bit little-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_i32_le;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0xFF, 0xFF, 0x03, 0x7];
    /// let o = parse_i32_le(&mut i);
    /// assert_eq!(o, Ok(0xFFFFFFFEu32 as i32));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_i32_le { i32, to_le };

    /// Parse a signed 64-bit little-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_i64_le;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x7];
    /// let o = parse_i64_le(&mut i);
    /// assert_eq!(o, Ok(0xFFFFFFFFFFFFFFFEu64 as i64));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_i64_le { i64, to_le };

    /// Parse a signed 128-bit little-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_i128_le;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    /// 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x7];
    /// let o = parse_i128_le(&mut i);
    /// assert_eq!(o, Ok(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEu128 as i128));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_i128_le { i128, to_le };

    // Signed big-endian integers

    /// Parse a signed 16-bit big-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_i16_be;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0x03, 0x7];
    /// let o = parse_i16_be(&mut i);
    /// assert_eq!(o, Ok(0xFEFFu16 as i16));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_i16_be { i16, to_be };

    /// Parse a signed 32-bit big-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_i32_be;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0xFF, 0xFF, 0x03, 0x7];
    /// let o = parse_i32_be(&mut i);
    /// assert_eq!(o, Ok(0xFEFFFFFFu32 as i32));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_i32_be { i32, to_be };

    /// Parse a signed 64-bit big-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_i64_be;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x7];
    /// let o = parse_i64_be(&mut i);
    /// assert_eq!(o, Ok(0xFEFFFFFFFFFFFFFFu64 as i64));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_i64_be { i64, to_be };

    /// Parse a signed 128-bit big-endian integer.
    ///
    /// ```rust
    /// use bytemuck_parsing::parse_i128_be;
    ///
    /// let mut i: &[u8] = &[0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    /// 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x03, 0x7];
    /// let o = parse_i128_be(&mut i);
    /// assert_eq!(o, Ok(0xFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFu128 as i128));
    /// assert_eq!(i, &[0x03, 0x7]);
    /// ```
    pub fn parse_i128_be { i128, to_be };
}

pub struct ParseFloatError<T>(pub ParseError, PhantomData<T>);

impl<T> ParseFloatError<T> {
    pub fn into_inner(self) -> ParseError {
        self.0
    }
}

impl<T> From<ParseError> for ParseFloatError<T> {
    fn from(x: ParseError) -> Self {
        Self(x, Default::default())
    }
}

impl<T> core::fmt::Display for ParseFloatError<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

/// Parse a 32-bit float.
///
/// ```rust
/// use bytemuck_parsing::parse_f32;
///
/// let i = [(42.0f32).to_bits().to_le_bytes().as_slice(), &[0x03, 0x7]].concat();
/// let mut i = i.as_slice();
/// let o = parse_f32(&mut i);
/// assert_eq!(o, Ok(42.0));
/// assert_eq!(i, &[0x03, 0x7])
/// ```
pub fn parse_f32(input: &mut &[u8]) -> Result<f32, ParseError> {
    let int: u32 = parse(input)?;
    let float = f32::from_bits(int);
    Ok(float)
}

/// Parse a 32-bit float.
///
/// ```rust
/// use bytemuck_parsing::parse_f64;
///
/// let i = [(42.0f64).to_bits().to_le_bytes().as_slice(), &[0x03, 0x7]].concat();
/// let mut i = i.as_slice();
/// let o = parse_f64(&mut i);
/// assert_eq!(o, Ok(42.0));
/// assert_eq!(i, &[0x03, 0x7])
/// ```
pub fn parse_f64(input: &mut &[u8]) -> Result<f64, ParseError> {
    let int: u64 = parse(input)?;
    let float = f64::from_bits(int);
    Ok(float)
}
