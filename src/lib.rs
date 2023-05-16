//! This crate provides a C# code generator for the `ffi_reflect` crate.
//! The code generator is implemented as a function that takes a root types definitions
//! and writes C# code into the `std::io::Write`.
//! For details see the function description.
//!
//! Note that array implementation is not absolutely safe due to C# limitations.
//! Be careful with references to array items,
//! because it is possible to create a dangling reference.
//!
//! Also, if you want to disable array bounds checking in the generated code,
//! define the `FFI_REFLECT_NO_BOUNDS_CHECK`.

use convert_case::{Case, Casing};
use ffi_reflect::{FfiArray, FfiEnum, FfiEnumUnderlyingType, FfiPrimitive, FfiStruct, FfiType};
use std::collections::VecDeque;
use std::collections::{HashMap, HashSet};
use std::io;
use std::io::Write;
use std::mem::{align_of, size_of};

/// Write C# code required to represent given `root_types`.
///
/// # Example
/// ```no_run
/// use std::collections::HashMap;
/// use std::fs::File;
/// use std::io::BufWriter;
/// use ffi_reflect::FfiReflect;
///
/// #[derive(FfiReflect)]
/// #[repr(C)]
/// struct World {
///     pub monsters: [Monster; 5],
/// }
///
/// #[derive(FfiReflect)]
/// #[repr(C)]
/// struct Monster {
///     pub position: MyVector,
///     pub hit_points: f32,
///     pub state: MonsterState,
/// }
///
/// #[derive(FfiReflect)]
/// #[repr(C)]
/// struct MyVector {
///     pub x: f32,
///     pub y: f32,
/// }
///
/// #[derive(FfiReflect)]
/// #[repr(u8)]
/// enum MonsterState { Idle = 0, Walking = 1 }
///
/// let mut writer = BufWriter::new(File::create("World.g.cs").unwrap());
/// let root_types = &[World::ffi_reflect()];
/// let namespace = "Sample.NameSpace";
/// let usings = &["UnityEngine"];
/// let type_mapping: HashMap<&str,&str> = HashMap::from([("MyVector", "Vector2")]);
/// ffi_reflect_csharp::write_types(&mut writer, root_types, namespace, usings, &type_mapping).unwrap();
/// ```
pub fn write_types<W: Write>(
    writer: &mut W,
    root_types: &[&'static FfiType],
    namespace: &str,
    usings: &[&str],
    type_mapping: &HashMap<&str, &str>,
) -> io::Result<()> {
    let mut written: HashSet<String> = HashSet::with_capacity(256);
    for k in type_mapping.keys() {
        written.insert(k.to_string());
    }

    writeln!(writer, "using System;")?;
    writeln!(writer, "using System.Runtime.InteropServices;")?;
    for using in usings {
        writeln!(writer, "using {};", using)?;
    }
    writeln!(writer)?;
    writeln!(writer, "namespace {} {{", namespace)?;

    let mut write_queue = VecDeque::with_capacity(root_types.len() * 2);
    for root_type in root_types {
        write_queue.push_back(*root_type);
    }

    while !write_queue.is_empty() {
        let ffi_type = write_queue.pop_front().unwrap();
        write_recursive(
            ffi_type,
            writer,
            &mut written,
            type_mapping,
            &mut write_queue,
        )?;
    }

    writeln!(writer, "}}")?;

    Ok(())
}

const I1: &str = "    ";
const I2: &str = "        ";
const I3: &str = "            ";

fn write_recursive<W: Write>(
    ffi_type: &'static FfiType,
    w: &mut W,
    written: &mut HashSet<String>,
    type_mapping: &HashMap<&str, &str>,
    write_queue: &mut VecDeque<&FfiType>,
) -> io::Result<()> {
    match ffi_type {
        FfiType::Primitive(_) => {}
        FfiType::Enum(e) => {
            if !written.contains(e.name) {
                write_enum(e, w)?;
                written.insert(e.name.to_string());
            }
        }
        FfiType::Struct(s) => {
            if !written.contains(s.name) {
                for field in s.fields {
                    write_recursive(field.field_type, w, written, type_mapping, write_queue)?;
                }
                write_struct(s, false, w, type_mapping)?;
                written.insert(String::from(s.name));
            }
        }
        FfiType::Union(u) => {
            if !written.contains(u.name) {
                for field in u.fields {
                    write_recursive(field.field_type, w, written, type_mapping, write_queue)?;
                }
                write_struct(u, true, w, type_mapping)?;
                written.insert(String::from(u.name));
            }
        }
        FfiType::Array(a) => {
            write_recursive(a.item_type, w, written, type_mapping, write_queue)?;
            if !written.contains(a.name) {
                write_array(a, w, type_mapping)?;
                written.insert(String::from(a.name));
            }
        }
        FfiType::Pointer(p) => {
            let pointed_type = (p.get_type)();
            if let FfiType::Primitive(_) = pointed_type {
            } else {
                write_queue.push_back(pointed_type);
            }
        }
    }

    Ok(())
}

fn write_enum<W: Write>(e: &FfiEnum, w: &mut W) -> io::Result<()> {
    let ut = get_underlying_type_str(e.underlying_type);

    writeln!(w, "{}public enum {} : {} {{", I1, e.name, ut)?;

    for (idx, entry) in e.values.iter().enumerate() {
        let last_idx = e.values.len() - 1;
        let sep = if idx != last_idx { "," } else { "" };
        writeln!(w, "{}{} = {}{}", I2, entry.name, entry.value, sep)?;
    }

    writeln!(w, "{}}}\n", I1)?;
    Ok(())
}

const fn get_underlying_type_str(ut: FfiEnumUnderlyingType) -> &'static str {
    match ut {
        FfiEnumUnderlyingType::U8 => "byte",
        FfiEnumUnderlyingType::U16 => "ushort",
        FfiEnumUnderlyingType::U32 => "uint",
        FfiEnumUnderlyingType::U64 => "ulong",
        FfiEnumUnderlyingType::I8 => "sbyte",
        FfiEnumUnderlyingType::I16 => "short",
        FfiEnumUnderlyingType::I32 => "int",
        FfiEnumUnderlyingType::I64 => "long",
    }
}

fn write_struct<W: Write>(
    s: &FfiStruct,
    is_union: bool,
    w: &mut W,
    type_mapping: &HashMap<&str, &str>,
) -> io::Result<()> {
    writeln!(w, "{}[StructLayout(LayoutKind.Sequential)]", I1)?;
    writeln!(w, "{}public struct {} {{", I1, s.name)?;

    writeln!(w, "{}public const int SizeOf = {};", I2, s.size)?;
    writeln!(w, "{}public const int AlignmentOf = {};", I2, s.align)?;
    writeln!(w)?;

    for f in s.fields {
        let field_type = get_type_str(f.field_type, type_mapping);
        let field_name = f.field_name.to_case(Case::UpperCamel);

        if is_union {
            writeln!(w, "{I2}[FieldOffset(0)]")?;
        }
        if field_type == "bool" {
            writeln!(w, "{I2}[MarshalAs(UnmanagedType.U1)]")?;
        }
        writeln!(w, "{I2}public {} {};", field_type, field_name)?;
    }

    writeln!(w, "{I1}}}\n")?;
    Ok(())
}

fn write_array<W: Write>(
    a: &FfiArray,
    w: &mut W,
    type_mapping: &HashMap<&str, &str>,
) -> io::Result<()> {
    writeln!(w, "{}[StructLayout(LayoutKind.Sequential)]", I1)?;
    writeln!(w, "{}public unsafe struct {} {{", I1, a.name)?;
    {
        let (size, align) = get_type_size_and_align(a.item_type);
        let size = size * a.item_count;

        writeln!(w, "{}public const int SizeOf = {};", I2, size)?;
        writeln!(w, "{}public const int AlignmentOf = {};", I2, align)?;
        writeln!(w, "{}public const int Length = {};", I2, a.item_count)?;
        writeln!(w, "{}private fixed byte _buffer[SizeOf];", I2)?;
    }
    writeln!(w, "{}}}\n", I1)?;

    writeln!(w, "{}public static unsafe class {}_IdxExt {{", I1, a.name)?;
    write_indexer(a, true, w, type_mapping)?;
    write_indexer(a, false, w, type_mapping)?;
    writeln!(w, "{I1}}}\n")?;
    Ok(())
}

fn write_indexer<W: Write>(
    a: &FfiArray,
    readonly: bool,
    w: &mut W,
    type_mapping: &HashMap<&str, &str>,
) -> io::Result<()> {
    let t = a.name;
    let t_item = get_type_str(a.item_type, type_mapping);

    let (method, mod_ret, mod_arg) = if readonly {
        ("RefReadonlyAt", "ref readonly", "in")
    } else {
        ("RefAt", "ref", "ref")
    };

    write!(w, "{}public static {} {} {}", I2, mod_ret, t_item, method)?;
    writeln!(w, "({} this {} a, int i) {{", mod_arg, t)?;

    writeln!(w, "#if !FFI_REFLECT_NO_BOUNDS_CHECK")?;
    writeln!(
        w,
        "{}if (i < 0 || i >= {}.Length) throw new IndexOutOfRangeException();",
        I3, t
    )?;
    writeln!(w, "#endif")?;

    write!(w, "{}fixed ({}* p = &a) ", I3, t)?;
    writeln!(w, "return ref *(({}*)p + i);", t_item)?;

    writeln!(w, "{I2}}}\n")?;
    Ok(())
}

fn get_type_str(t: &FfiType, type_mapping: &HashMap<&str, &str>) -> String {
    match t {
        FfiType::Primitive(p) => match p {
            FfiPrimitive::BOOL => "bool",
            FfiPrimitive::U8 => "byte",
            FfiPrimitive::U16 => "ushort",
            FfiPrimitive::U32 => "uint",
            FfiPrimitive::U64 => "ulong",
            FfiPrimitive::I8 => "sbyte",
            FfiPrimitive::I16 => "short",
            FfiPrimitive::I32 => "int",
            FfiPrimitive::I64 => "long",
            FfiPrimitive::F32 => "float",
            FfiPrimitive::F64 => "double",
        }
        .to_string(),
        FfiType::Enum(e) => e.name.to_string(),
        FfiType::Struct(s) => type_mapping.get(s.name).unwrap_or(&s.name).to_string(),
        FfiType::Union(u) => u.name.to_string(),
        FfiType::Array(a) => a.name.to_string(),
        FfiType::Pointer(p) => {
            let pointed_type = (p.get_type)();
            let pointed_type_str = get_type_str(pointed_type, type_mapping);
            format!("{}*", pointed_type_str)
        }
    }
}

fn get_type_size_and_align(t: &FfiType) -> (usize, usize) {
    match t {
        FfiType::Primitive(p) => get_primitive_size_and_align(p),
        FfiType::Enum(e) => get_enum_size_and_align(&e.underlying_type),
        FfiType::Struct(s) | FfiType::Union(s) => (s.size, s.align),
        FfiType::Array(a) => {
            let (size, align) = get_type_size_and_align(a.item_type);
            (size * a.item_count, align)
        }
        FfiType::Pointer(_) => (size_of::<usize>(), align_of::<usize>()),
    }
}

fn get_enum_size_and_align(u: &FfiEnumUnderlyingType) -> (usize, usize) {
    match u {
        FfiEnumUnderlyingType::U8 => (size_of::<u8>(), align_of::<u8>()),
        FfiEnumUnderlyingType::U16 => (size_of::<u16>(), align_of::<u16>()),
        FfiEnumUnderlyingType::U32 => (size_of::<u32>(), align_of::<u32>()),
        FfiEnumUnderlyingType::U64 => (size_of::<u64>(), align_of::<u64>()),
        FfiEnumUnderlyingType::I8 => (size_of::<i8>(), align_of::<i8>()),
        FfiEnumUnderlyingType::I16 => (size_of::<i16>(), align_of::<i16>()),
        FfiEnumUnderlyingType::I32 => (size_of::<i32>(), align_of::<i32>()),
        FfiEnumUnderlyingType::I64 => (size_of::<i64>(), align_of::<i64>()),
    }
}

fn get_primitive_size_and_align(p: &FfiPrimitive) -> (usize, usize) {
    match p {
        FfiPrimitive::BOOL => (size_of::<bool>(), align_of::<bool>()),
        FfiPrimitive::U8 => (size_of::<u8>(), align_of::<u8>()),
        FfiPrimitive::U16 => (size_of::<u16>(), align_of::<u16>()),
        FfiPrimitive::U32 => (size_of::<u32>(), align_of::<u32>()),
        FfiPrimitive::U64 => (size_of::<u64>(), align_of::<u64>()),
        FfiPrimitive::I8 => (size_of::<i8>(), align_of::<i8>()),
        FfiPrimitive::I16 => (size_of::<i16>(), align_of::<i16>()),
        FfiPrimitive::I32 => (size_of::<i32>(), align_of::<i32>()),
        FfiPrimitive::I64 => (size_of::<i64>(), align_of::<i64>()),
        FfiPrimitive::F32 => (size_of::<f32>(), align_of::<f32>()),
        FfiPrimitive::F64 => (size_of::<f64>(), align_of::<f64>()),
    }
}
