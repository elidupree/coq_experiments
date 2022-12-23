#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct OpaqueIndexRepresentative(usize);

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
struct IndexClassId(usize);

#[derive(Debug)]
enum IndexRepresentativeInfo {
    MainOfClass(IndexClassId),
    DelegatedTo(OpaqueIndexRepresentative),
}

#[derive(Debug)]
struct IndexClassInfo {
    main_representative: OpaqueIndexRepresentative,
    must_not_equal: Vec<IndexClassId>,
}

#[derive(Default, Debug)]
pub struct IdentifiableIndices {
    representatives: Vec<IndexRepresentativeInfo>,
    classes: Vec<IndexClassInfo>,
}

impl IdentifiableIndices {
    pub fn new() -> Self { Self::default() }
    fn get_main_of_class(&mut self, r: OpaqueIndexRepresentative) -> (OpaqueIndexRepresentative, IndexClassId) {
        match self.representatives[r.0] {
            IndexRepresentativeInfo::MainOfClass(class_id) => { (r, class_id) }
            IndexRepresentativeInfo::DelegatedTo(next) => {
                let (main, class_id) = self.get_main_of_class(next);
                self.representatives[r.0] = IndexRepresentativeInfo::DelegatedTo(next);
                (main, class_id)
            }
        }
    }
    fn get_class_id(&mut self, r: OpaqueIndexRepresentative) -> IndexClassId {
        self.get_main_of_class(r).1
    }
    pub fn make_new_index(&mut self) -> OpaqueIndexRepresentative {
        self.representatives.push(IndexRepresentativeInfo::MainOfClass(IndexClassId(self.classes.len())));
        self.classes.push(IndexClassInfo { main_representative: OpaqueIndexRepresentative(self.representatives.len() - 1), must_not_equal: vec![] });
        OpaqueIndexRepresentative(self.representatives.len() - 1)
    }
    fn move_backrefs(&mut self, class_id: IndexClassId, new_id: IndexClassId) {
        self.representatives[self.classes[class_id.0].main_representative.0] = IndexRepresentativeInfo::MainOfClass(new_id);
        for exclusion in self.classes[class_id.0].must_not_equal.clone() {
            for back_reference in &mut self.classes[exclusion.0].must_not_equal {
                if *back_reference == class_id { *back_reference = new_id }
            }
            self.classes[exclusion.0].must_not_equal.sort();
            self.classes[exclusion.0].must_not_equal.dedup();
        }
    }
    pub fn try_identify(&mut self, r1: OpaqueIndexRepresentative, r2: OpaqueIndexRepresentative) -> Result<(), ()> {
        let c1 = self.get_class_id(r1);
        let c2 = self.get_class_id(r2);
        if c1 == c2 { return Ok(()); }
        if self.classes[c1.0].must_not_equal.contains(&c2) { return Err(()); }
        self.move_backrefs(c2, c1);
        self.move_backrefs(IndexClassId(self.classes.len() - 1), c2);
        self.representatives[self.classes[c2.0].main_representative.0] = IndexRepresentativeInfo::DelegatedTo(self.classes[c1.0].main_representative);
        let taken = self.classes[c2.0].must_not_equal.clone();
        self.classes[c1.0].must_not_equal.extend_from_slice(&taken);
        self.classes[c1.0].must_not_equal.sort();
        self.classes[c1.0].must_not_equal.dedup();
        self.classes.swap_remove(c2.0);
        Ok(())
    }
    pub fn try_exclude(&mut self, r1: OpaqueIndexRepresentative, r2: OpaqueIndexRepresentative) -> Result<(), ()> {
        let c1 = self.get_class_id(r1);
        let c2 = self.get_class_id(r2);
        if c1 == c2 { return Err(()); }
        if self.classes[c1.0].must_not_equal.contains(&c2) { return Ok(()); }
        self.classes[c1.0].must_not_equal.push(c2);
        self.classes[c2.0].must_not_equal.push(c1);
        Ok(())
    }
    pub fn short_name(&mut self, r: OpaqueIndexRepresentative) -> usize {
        self.get_class_id(r).0
    }
}

fn main() {
    let mut indices = IdentifiableIndices::new();
    let a = indices.make_new_index();
    let b = indices.make_new_index();
    println!("{}, {}", indices.short_name(a), indices.short_name(b));
    println!("{:?}", indices.try_identify(a, b));
    println!("{}, {}", indices.short_name(a), indices.short_name(b));
    let c = indices.make_new_index();
    println!("{:?}", indices);
    println!("{:?}", (c, indices.get_main_of_class(c)));
    println!("{:?}", indices.try_exclude(a, b));
    println!("{:?}", indices.try_exclude(a, c));
    println!("{:?}", indices.try_identify(b, c));
    println!("{:?}", (indices.short_name(a), indices.short_name(b), indices.short_name(c)));
}