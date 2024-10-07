use super::*;


#[derive(Debug, Default, Clone)]
pub struct StringEntry
{
    name : String,
    nb_use : u32,
}

impl Display for StringEntry
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:10} ({} use)", self.name, self.nb_use)
    }
}

impl StringEntry
{
    pub fn name(&self) -> &str { &self.name }
    pub fn nb_use(&self) -> u32 { self.nb_use }
    
    pub fn use_inc(&mut self)
    {
        assert!(self.nb_use != u32::MAX, "wow you are using this symbol a lot !");
        self.nb_use += 1;
    }

    pub fn use_dec(&mut self)
    {
        assert!(self.nb_use > 0, "fix the symbol count");
        self.nb_use -= 1;
    }
}

/// A factorized string name
#[derive(Hash, PartialEq, Eq, Clone, Copy)]
pub struct StringID { val : StableVecID<StringEntry> }

impl Debug for StringID
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "StringID{:?}", self.val)
    }
}

impl StringID
{
    pub fn value(&self) -> usize { self.val.value() }
}

/* 
impl SymbolID
{
    pub fn as_reserved_symbol(self) -> ReservedSymbol
    {
        ReservedSymbol::try_from(self.0 as ReservedSymbolRep).unwrap()
    }
}*/

/// Factorize string into a simple id
#[derive(Debug, Default, Clone)]
pub struct StringTable
{
    all : StableVec<StringEntry>,
    search : HashMap<String, StringID>,
}

impl StringTable
{
    pub fn is_empty(&self) -> bool { self.all.is_empty() }
    
    pub fn iter(&self) -> impl Iterator<Item = &StringEntry> { self.all.iter() }
    pub fn iter_with_value(&self) -> impl Iterator<Item = (usize, &StringEntry)> 
    { self.all.iter_with_key().map(|(idx, val)| (idx.value(), val)) }

    pub fn new() -> Self { Self::___() }

    pub fn string_id_use_inc(&mut self, s : StringID) { self[s].use_inc(); }

    /// The only way to clone a string value
    pub fn string_id_clone(&mut self, s : StringID) -> StringID { self.string_id_use_inc(s); s }

    /// The only way to drop a symbol
    pub fn string_id_drop(&mut self, idx : StringID) 
    {
        let e = &mut self[idx];
        e.use_dec();

        if e.nb_use == 0
        {
            let mut name = "".to_owned();
            std::mem::swap(&mut name, &mut e.name);
            self.search.remove(&name);
        }
    }

    pub fn add(&mut self, name : String) -> StringID
    {
        match self.search.get(&name)
        {
            Some(s) => 
            { 
                let r = *s; 
                self.all[s.val].use_inc(); r
            },
            None => 
            {
                let symbol_id = StringID {val : self.all.push(StringEntry { name : name.clone(), nb_use: 1 }) };
                self.search.insert(name, symbol_id);
                symbol_id
            },
        }
    }
}

impl Index<StringID> for StringTable { type Output = StringEntry; fn index(&self, index: StringID) -> &Self::Output { &self.all[index.val] } }
impl IndexMut<StringID> for StringTable { fn index_mut(&mut self, index: StringID) -> &mut Self::Output { &mut self.all[index.val] }}
