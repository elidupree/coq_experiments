pub fn first_difference_index<T: PartialEq>(a: &[T], b: &[T]) -> Option<usize> {
    a.iter().zip(b).position(|(a, b)| a != b).or_else(|| {
        if a.len() == b.len() {
            None
        } else {
            Some(std::cmp::min(a.len(), b.len()))
        }
    })
}

macro_rules! capture_fields_mut {
    ($object: ident.{$($field: ident,)*}) => {
        $(let $field = &mut $object.$field;)*
    };
    ($object: ident.{$($field: ident),*}) => {
        capture_fields_mut!($object.{$($field,)*})
    };
    ($object: ident.$field: ident) => {
        capture_fields_mut!($object.{$field,})
    };
}
