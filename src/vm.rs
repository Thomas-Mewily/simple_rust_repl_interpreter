use std::{default, fmt::write};

use super::*;

type TrPtrContainer<T> = Rc<T>;
type VMTr = dyn Fn(&mut VM, TrCall) -> Expr + 'static;
type TrPtr = TrPtrContainer <VMTr>;

/// Stand for Transformations.
/// Transformation regroup function and macro
/// 
/// When evaluating a function, all argument are evaluated by the caller, then the function is called
/// Thank to this mecanism, it is possible to use function pointer
/// 
/// When evaluating a macro, it is the macro that decide when argument should be evaluted (or not).
/// The same argument can be evaluated as many time as you want : zero, once, twice...
/// Because of that, macro pointer are not possible, because what the macro do should be know at compile time
#[derive(Clone)]
pub struct Tr 
{
    closure : TrPtr,
    kind    : TrKind,
}
impl Tr
{
    pub fn new<T>(closure : T, kind : TrKind) -> Self 
        where T : Fn(&mut VM, TrCall) -> Expr + 'static
    { Self { closure : TrPtrContainer::new(closure), kind }}
}

#[derive(Clone, PartialEq, Eq)]
pub struct TrCall
{
    tr_follow_by_arg: Vec<Expr>,
}
impl Debug for TrCall{ fn fmt(&self, f: &mut Formatter<'_>) -> DResult { write!(f, "{:?}", self.tr_follow_by_arg) } }
impl TrCall
{
    pub fn new(arg: Vec<Expr>) -> Self { Self { tr_follow_by_arg: arg }}

    fn err_postfix(&self, vm : &VM) -> String { format!("\n> {}", vm.display(&self.tr().kind(vm))) }
    
    pub fn end_arg(&self, vm : &VM, index : usize) -> Result<(), String> 
    {
        if index == self.nb_args() 
        { Ok(()) } else { Err(format!("Only {} args where expected for `{}`{}", self.nb_args(), vm.display(self), self.err_postfix(vm))) }
    }

    pub fn next_arg(&self, vm : &VM, index : &mut usize) -> Result<(), String> 
    { *index += 1; Ok(()) }

    pub fn check_arg(&self, vm : &VM, index : &mut usize, description : &str, maybe_expected_kind : Option<Kind>) -> Result<(), String> 
    {
        if *index >= self.nb_args() 
        { return Err(format!("Missing arg {} `{}` for `{}`{}", *index+1, description, vm.display(self), self.err_postfix(vm))); }
        
        let got_kind = vm.try_kind_of(self.arg_at(*index))?;

        if let Some(expected_kind) = maybe_expected_kind
        {
            if got_kind != expected_kind
            {
                return Err(format!("Arg {} should be of type `{}` instead of `{}`{}", *index+1, vm.display(&expected_kind), vm.display(&got_kind), self.err_postfix(vm)));
            }
        }
        
        self.next_arg(vm, index)
    }


    pub fn tr(&self) -> &Expr { &self.tr_follow_by_arg[0]}
    pub fn nb_args(&self) -> usize { self.tr_follow_by_arg.len()-1 }
    pub fn args(&self) -> &[Expr] { &self.tr_follow_by_arg[1..] }
    pub fn arg_at(&self, idx: usize) -> &Expr { &self.tr_follow_by_arg[idx+1] }

    pub fn take_arg(&mut self, idx: usize) -> Expr { self.take_index(idx+1)}
    pub fn take_tr(&mut self) -> Expr { self.take_index(0)}


    pub fn take_index(&mut self, idx: usize) -> Expr { std::mem::replace(&mut self.tr_follow_by_arg[idx], Expr::Void) }

    pub fn iter(&self) -> impl Iterator<Item = &Expr> { self.tr_follow_by_arg.iter() }
    pub fn iter_arg(&self) -> impl Iterator<Item = &Expr> { self.tr_follow_by_arg.iter().skip(1) }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct TrID { idx : usize }
impl TrID { fn new(val : usize) -> Self { Self { idx: val }}}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TrKind
{
    BuildIn(TrBuildIn),
    External(TrKindExternal),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrKindExternal
{
    input_kind : Vec<Kind>,
    output : Kind,
    cat : TrCat,
}
impl TrKindExternal
{
    pub fn new(input_kind : Vec<Kind>, output : Kind, cat : TrCat) -> Self 
    {
        Self { input_kind, output, cat }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TrCat { Fn, Macro }
impl Display for TrCat { 
    fn fmt(&self, f: &mut Formatter<'_>) -> DResult 
    {
        match self
        {
            TrCat::Fn => f.write_str("fn"),
            TrCat::Macro => f.write_str("macro"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TrBuildIn
{
    /// (template T (if cond:bool true_val:'T false_val:'T))
    IfElse,
    /// (loop expr)
    Loop,
    /// (break label value)
    Break,
    /// (continue label)
    Continue,
    /// (typeof expr)
    KindOf,
}

#[derive(Clone, Debug)]
pub enum Kind
{
    Void, I32, Bool, 
    Kind,
    Tr(Box<TrKind>),
    /// An Expression
    Any
}
impl Eq for Kind {}
impl PartialEq for Kind
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) 
        {
            (Self::Any, _) | (_, Self::Any) => true,
            (Self::Tr(l0), Self::Tr(r0)) => l0 == r0,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

impl Kind
{
    pub fn is_void(&self) -> bool { matches!(self, Kind::Void) }
    pub fn is_any(&self) -> bool { matches!(self, Kind::Any) }
}


impl VM
{
    pub fn kind_of_tr(&self, tr_id : TrID) -> TrKind { self[tr_id].kind.clone() }
    pub fn kind_of(&self, e : &Expr) -> Kind { self.try_kind_of(e).unwrap() }

    pub fn try_kind_of(&self, e : &Expr) -> Result<Kind, String>
    {
        match e
        {
            Expr::Void => Ok(Kind::Void),
            Expr::I32(_) => Ok(Kind::I32),
            Expr::Bool(_) => Ok(Kind::Bool),
            Expr::Kind(_) => Ok(Kind::Kind),

            Expr::Symb(s) => Ok(self[*s].value().kind(self)),

            Expr::Tr(tr) => Ok(Kind::Tr(Box::new(self[*tr].kind.clone()))),
            Expr::TrCall(tr) => 
            {
                let t = tr.tr();
                let Kind::Tr(t) = t.kind(self) else { return Err(format!("`{}` is not a function/macro", self.display(t))); };
                match *t
                {
                    TrKind::BuildIn(bi) => 
                    {
                        match bi
                        {
                            TrBuildIn::IfElse => 
                            {
                                let true_val_kind = tr.arg_at(1).kind(self);
                                let false_val_kind = tr.arg_at(2).kind(self);
                                if true_val_kind != false_val_kind 
                                {
                                    Err(format!("if block don't have the same branch kind\n`{}` vs `{}`", self.display(&true_val_kind), self.display(&false_val_kind)))
                                }else
                                {
                                    Ok(true_val_kind)
                                }
                            },
                            TrBuildIn::Loop => todo!(),
                            TrBuildIn::Break => todo!(),
                            TrBuildIn::Continue => todo!(),
                            TrBuildIn::KindOf => Ok(Kind::Kind),
                        }
                    },
                    TrKind::External(ex) => Ok(ex.output),
                }
            }

            Expr::Break(_, _) => panic!("break are special"),
            Expr::Continue(_) => panic!("continue are special"),
        }
    }
}


#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr
{
    Void, I32(i32), Bool(bool),

    Kind(Kind),

    Symb(SymbID),
    
    /// Not supposed to get evaluated, and can't be created except by the (break nested expr) macro
    Break(NestedLevel, Box<Expr>),
    /// Not supposed to get evaluated, and can't be created except by the (continue nested) macro
    Continue(NestedLevel),

    Tr(TrID), TrCall(TrCall),
}
impl From<()> for Expr { fn from(_value : ()) -> Self { Expr::Void }}
impl From<i32> for Expr { fn from(value : i32) -> Self { Expr::I32(value) }}
impl From<bool> for Expr { fn from(value : bool) -> Self { Expr::Bool(value) }}
impl From<Kind> for Expr { fn from(value : Kind) -> Self { Expr::Kind(value) }}
impl From<TrCall> for Expr { fn from(value : TrCall) -> Self { Expr::TrCall(value) }}

impl TryFrom<&Expr> for () { type Error=(); fn try_from(value: &Expr) -> Result<Self, Self::Error> { match value { Expr::Void => Ok(()), _ => { Err(())} } }}
impl TryFrom<&Expr> for i32 { type Error=(); fn try_from(value: &Expr) -> Result<Self, Self::Error> { match value { Expr::I32(v) => Ok(*v), _ => { Err(())} } }}
impl TryFrom<&Expr> for bool { type Error=(); fn try_from(value: &Expr) -> Result<Self, Self::Error> { match value { Expr::Bool(v) => Ok(*v), _ => { Err(())} } }}

#[derive(Default)]
pub struct VM
{
    /// Factorized string for symbol name
    string_table : StringTable,

    /// A tree containing the symbols definitions and how we can refer to them
    env : Env,

    tr_table: Vec<Tr>,

    permission : Permission,

    /// For parsing Lisp style code
    parser : Parser,
}

#[derive(Default, Clone)]
pub struct Permission
{
    /// If the VM can branch at any point. Also include match/switch/cond
    branching_if    : Option<SymbID>,
    /// infinite loop
    looping         : Option<SymbID>,
    /// for breaking infinite loop
    break_label     : Option<SymbID>,
    /// for continuing infinite loop
    continue_label : Option<SymbID>,
    /// getting the type of an expression
    kind_of : Option<SymbID>,
}

impl VM
{
    pub fn new() -> Self { ___() }
}
impl Index<TrID> for VM { type Output=Tr; fn index(&self, index: TrID) -> &Self::Output { &self.tr_table[index.idx] } }
impl Index<SymbID> for VM { type Output=Symbol; fn index(&self, index: SymbID) -> &Self::Output { &self.env[index] }}
impl Index<StringID> for VM { type Output=str; fn index(&self, index: StringID) -> &Self::Output { self.string_table[index].name() }}

impl Expr
{
    pub fn eval(self, vm : &mut VM) -> Expr { vm.eval(self) }
    pub fn kind(&self, vm : &VM) -> Kind { vm.kind_of(self) }

    pub fn to_void(&self) { <()>::try_from(self).unwrap() }
    pub fn to_i32(&self) -> i32 { i32::try_from(self).unwrap() }
    pub fn to_bool(&self) -> bool { bool::try_from(self).unwrap() }
    pub fn to_tr(&self) -> TrID { match self { Expr::Tr(v) => *v, _ => panic!() }}

    pub fn to_nested_level(&self) -> NestedLevel { self.to_i32() as NestedLevel }
}
type NestedLevel = u32;

impl VM
{
    pub fn eval(&mut self, expr : Expr) -> Expr
    { 
        use Expr::*;
        match expr
        {
            x @ Void => x,
            x @ I32(_) => x,
            x @ Bool(_) => x,
            x @ Kind(_) => x,
            x @ Tr(_) => x,

            Symb(s) => self[s].value().clone().eval(self),
            TrCall(mut tr) => 
            {
                let f = tr.take_index(0);
                let tr_id = self.eval(f).to_tr();
                let closure = self[tr_id].closure.clone();
                (closure)(self, tr)
            }

            Break(_, _) => panic!("Break can't be eval"),
            Continue(_) => panic!("Continue can't be eval"),
        }
    }
}

// ================= VmAdd =================
pub trait VmAdd<T> : Sized
{
    fn get_expr(self, vm : &mut VM) -> Expr;
    fn add(self, vm : &mut VM) -> SymbID { let e = self.get_expr(vm); vm.add_expr(e) }
}
impl VmAdd<()> for () { fn get_expr(self, vm : &mut VM) -> Expr { self.into() }}
impl VmAdd<()> for i32 { fn get_expr(self, vm : &mut VM) -> Expr { self.into() }}
impl VmAdd<()> for bool { fn get_expr(self, vm : &mut VM) -> Expr { self.into() }}
impl VmAdd<()> for Kind { fn get_expr(self, vm : &mut VM) -> Expr { self.into() }}

impl VM
{
    fn add_lambda_if(&mut self) -> SymbID
    {
        if self.permission.branching_if.is_none()
        {
            let v = Expr::Tr(self._build_in_add_tr(
                Tr::new(
                    |vm, mut arg|
                    if arg.take_arg(0).eval(vm).to_bool() 
                    { arg.take_arg(1).eval(vm) } else { arg.take_arg(2).eval(vm) },
                    TrKind::BuildIn(TrBuildIn::IfElse)
                )
            ));
            self.permission.branching_if = Some(self.add_expr(v));
        }
        self.permission.branching_if.unwrap()
    }

    fn add_lambda_loop(&mut self) -> SymbID
    {
        if self.permission.looping.is_none()
        {
            let v = Expr::Tr(self._build_in_add_tr(
                Tr::new(
                    |vm, mut arg|
                    {
                        let body = arg.take_arg(0);
                        loop
                        {
                            let e = body.clone().eval(vm);
                            match e
                            {
                                Expr::Break(nested, val) => 
                                { return if nested == 0 { *val } else { Expr::Break(nested-1, val) }},
                                Expr::Continue(nested) => 
                                { if nested != 0 { return Expr::Continue(nested-1) }},
                                _ => {}
                            };
                        }
                    },
                    TrKind::BuildIn(TrBuildIn::Loop)
                )
            ));
            self.permission.looping = Some(self.add_expr(v));
        }
        self.permission.looping.unwrap()
    }

    
    fn add_lambda_break(&mut self) -> SymbID
    {
        if self.permission.break_label.is_none()
        {
            let v = Expr::Tr(self._build_in_add_tr(
                Tr::new(
                    |vm, mut arg|
                    {
                        let nested = arg.take_arg(0).to_nested_level();
                        let return_val = arg.take_arg(1).eval(vm);
                        Expr::Break(nested, Box::new(return_val))
                    },
                    TrKind::BuildIn(TrBuildIn::Break)
                )
            ));
            self.permission.break_label = Some(self.add_expr(v));
        }
        self.permission.break_label.unwrap()
    }

    fn add_lambda_continue(&mut self) -> SymbID
    {
        if self.permission.continue_label.is_none()
        {
            let v = Expr::Tr(self._build_in_add_tr(
                Tr::new(
                    |vm, mut arg|
                    {
                        let nested = arg.take_arg(0).to_nested_level();
                        Expr::Continue(nested)
                    },
                    TrKind::BuildIn(TrBuildIn::Continue)
                )
            ));
            self.permission.continue_label = Some(self.add_expr(v));
        }
        self.permission.continue_label.unwrap()
    }

    fn add_lambda_kind_of(&mut self) -> SymbID
    {
        if self.permission.kind_of.is_none()
        {
            let v = Expr::Tr(self._build_in_add_tr(
                Tr::new(
                    |vm, mut arg|
                    { vm.kind_of(&arg.take_arg(0)).into() },
                    TrKind::BuildIn(TrBuildIn::KindOf)
                )
            ));
            self.permission.kind_of = Some(self.add_expr(v));
        }
        self.permission.kind_of.unwrap()
    }
}
impl VmAdd<()> for TrBuildIn
{
    fn add(self, vm : &mut VM) -> SymbID 
    {
        match self
        {
            TrBuildIn::IfElse => vm.add_lambda_if(),
            TrBuildIn::Loop => vm.add_lambda_loop(),
            TrBuildIn::Break => vm.add_lambda_break(),
            TrBuildIn::Continue => vm.add_lambda_continue(),
            TrBuildIn::KindOf => vm.add_lambda_kind_of(),
        }
    }
    fn get_expr(self, vm : &mut VM) -> Expr { panic!("can get the build in {} outside in Rust", vm.display(self)) }
}


impl<F, P0, E> VmAdd<(P0, E)> for F
    where 
        F : for <'a> Fn(P0) -> E + 'static,
        P0 : FromVM,
        E : Into<Expr> + FromVM
{
    fn get_expr(self, vm : &mut VM) -> Expr 
    {
        let f = move |vm : &mut VM, mut arg: TrCall| 
            { 
                let p0 = P0::from_vm(vm, arg.take_arg(0));
                let e : Expr = (self)(p0).into();
                e
            };

        let t = TrKind::External(TrKindExternal::new(vec![P0::get_type(vm)], E::get_type(vm), TrCat::Fn));
        Expr::Tr(vm._build_in_add_tr(Tr::new(f, t)))
    }
}

impl<F, P0, P1, E> VmAdd<(P0, P1, E)> for F
    where 
        F : for <'a> Fn(P0, P1) -> E + 'static,
        P0 : FromVM, P1 : FromVM,
        E : Into<Expr> + FromVM
{
    fn get_expr(self, vm : &mut VM) -> Expr 
    {
        let f = move |vm : &mut VM, mut arg: TrCall| 
            { 
                let p0 = P0::from_vm(vm, arg.take_arg(0));
                let p1 = P1::from_vm(vm, arg.take_arg(1));
                let e : Expr = (self)(p0, p1).into();
                e
            };

        let t = TrKind::External(TrKindExternal::new(vec![P0::get_type(vm), P1::get_type(vm)], E::get_type(vm), TrCat::Fn));
        Expr::Tr(vm._build_in_add_tr(Tr::new(f, t)))
    }
}

// ================= FromVM =================
pub trait FromVM 
{
    fn get_type(vm : &mut VM) -> Kind;

    fn from_vm(vm : &mut VM, e: Expr) -> Self where Self : Sized { Self::quoted_arg(vm, e, 0) }
    fn quoted_arg(vm : &mut VM, e: Expr, idx : usize) -> Self where Self : Sized
    { 
        let evaluated = vm.eval(e); 
        Self::evalutated_arg(vm, evaluated, idx)
    }

    fn evalutated_arg(vm : &mut VM, e: Expr, idx : usize) -> Self where Self : Sized { panic!() }
}

impl FromVM for Expr { 
    fn evalutated_arg(vm : &mut VM, e : Expr, _idx : usize) -> Self { e }
    fn get_type(vm : &mut VM) -> Kind { Kind::Any }
}
impl FromVM for () { 
    fn evalutated_arg(vm : &mut VM, e : Expr, _idx : usize) -> Self { e.to_void() }
    fn get_type(vm : &mut VM) -> Kind { Kind::Void }
}
impl FromVM for i32 { 
    fn evalutated_arg(vm : &mut VM, e : Expr, _idx : usize) -> Self { e.to_i32() }
    fn get_type(vm : &mut VM) -> Kind { Kind::I32 }
}
impl FromVM for bool { 
    fn evalutated_arg(vm : &mut VM, e : Expr, _idx : usize) -> Self { e.to_bool() }
    fn get_type(vm : &mut VM) -> Kind { Kind::Bool }
}


/// Env :


#[derive(Debug)]
pub struct Env
{
    /// indexed by Env
    all : StableVec<Symbol>,
    
    scopes : Vec<SymbID>,
}

impl Index<SymbID> for Env { type Output=Symbol; fn index(&self, index: SymbID) -> &Self::Output { &self.all[index] } }
impl IndexMut<SymbID> for Env { fn index_mut(&mut self, index: SymbID) -> &mut Self::Output { &mut self.all[index] } }

impl Default for Env { fn default() -> Self { Self::root() } }

impl Env
{
    pub fn root() -> Self
    {
        let mut all = StableVec::___();
        all.push(Symbol{_value:Expr::Symb(___()),_scope:___(),_childs:___(), _named: ___() });
        Self { all, scopes : vec![SymbID::new(0)] }
    }

    pub fn push_scope(&mut self, symb_id : SymbID) { self.scopes.push(symb_id) }
    pub fn pop_scope(&mut self) -> SymbID 
    { 
        assert!(self.scopes.len() >= 2, "scopes vec should never be empty");
        self.scopes.pop().unwrap()
    }
    pub fn scope_id(&self) -> SymbID { self.scopes[0] }
    pub fn scope(&self) -> &Symbol { &self[self.scope_id()] }

    fn add_symb(&mut self, value : Expr) -> SymbID
    { self.add_symb_inside(value, self.scope_id()) }
    fn add_symb_inside(&mut self, value : Expr, scope : SymbID) -> SymbID
    {
        let s = SymbID::new(self.all.len());
        self[scope]._childs.push(s);
        // Todo : maybe check what inside Expr?
        self.all.push(Symbol { _value : value, _scope: scope, _childs: ___(), _named: ___() });
        s
    }
}
impl VM
{
    pub fn push_scope(&mut self, symb_id : SymbID) { self.env.push_scope(symb_id) }
    pub fn pop_scope(&mut self) -> SymbID { self.env.pop_scope() }
    pub fn scope_id(&self) -> SymbID { self.env.scope_id() }
    pub fn scope(&self) -> &Symbol { self.env.scope() }
}
impl VM
{
    fn try_bind_string_id_to_symb(&mut self, string_id : StringID) -> Option<SymbID> { self.try_bind_string_id_to_symb_inside(string_id, self.scope_id()) }

    fn try_bind_string_id_to_symb_inside(&mut self, string_id : StringID, parent : SymbID) -> Option<SymbID> 
    {
        let mut id = parent;
        loop
        {
            if let Some(v) = self[id]._named.get(&string_id).copied()
            { 
                return Some(v) 
            }

            id = self[id].scope();
            if id.is_root() { return None; }
        }
    }

    pub fn add_expr(&mut self, value : Expr) -> SymbID
    { self.env.add_symb(value) }

    pub fn add_expr_inside(&mut self, value : Expr, parent : SymbID) -> SymbID
    { self.env.add_symb_inside(value, parent) }


    fn _build_in_add_tr(&mut self, tr : Tr) -> TrID
    {
        let id = TrID::new(self.tr_table.len());
        self.tr_table.push(tr);
        id
    }

    pub fn add_lambda<T : VmAdd<H>, H>(&mut self, t : T) -> SymbID 
    { 
        let e: SymbID = t.add(self);
        //println!("{:?}", self[e]);
        e
    }

    pub fn add_named_expr<T : VmAdd<H>, H>(&mut self, name : &str, t : T) -> SymbID { self.add(name, t) }
    pub fn add<T : VmAdd<H>, H>(&mut self, name : &str, t : T) -> SymbID 
    { 
        let s = self.add_lambda(t);
        self.add_name_in_parent(name.to_owned(), s)
    } 

    pub fn add_name(&mut self, name : String, val : SymbID) -> SymbID { self.add_name_in_scope(name, val) }
    pub fn add_name_in_parent(&mut self, name : String, val : SymbID) -> SymbID { self.add_name_inside(name, val, self.env[val].scope()) }
    pub fn add_name_in_scope(&mut self, name : String, val : SymbID) -> SymbID { self.add_name_inside(name, val, self.scope_id()) }
    
    pub fn add_name_inside(&mut self, name : String, val : SymbID, scope : SymbID) -> SymbID
    {
        let n = self.string_table.add(name);

        match self.env[scope]._named.insert(n, val){
            Some(already_existing_name) => panic!("name {} is already defined", &self[n]),
            None => val,
        }
    }
}

pub trait Keywords
{
    fn add_to_vm(self, vm : &mut VM, symb : SymbID);
}

impl Keywords for &str { fn add_to_vm(self, vm : &mut VM, symb : SymbID) { vm.add_name(self.to_owned(), symb);} }
impl Keywords for String { fn add_to_vm(self, vm : &mut VM, symb : SymbID) { vm.add_name(self, symb);} }
impl<T : Keywords> Keywords for Vec<T>
{
    fn add_to_vm(self, vm : &mut VM, symb : SymbID) {
        for t in self
        {
            t.add_to_vm(vm, symb)
        }
    }
}

impl VM
{
    fn _add_tr_build_in<T : Keywords>(&mut self, bi : TrBuildIn, kw : T) -> SymbID
    {
        let s = self.add_lambda(bi);
        kw.add_to_vm(self, s);
        s
    }

    pub fn add_if<T : Keywords>(&mut self, kw : T) -> SymbID { self._add_tr_build_in(TrBuildIn::IfElse, kw) }
    pub fn add_loop<T : Keywords>(&mut self, kw : T) -> SymbID { self._add_tr_build_in(TrBuildIn::Loop, kw) }
    pub fn add_break<T : Keywords>(&mut self, kw : T) -> SymbID { self._add_tr_build_in(TrBuildIn::Break, kw) }
    pub fn add_continue<T : Keywords>(&mut self, kw : T) -> SymbID { self._add_tr_build_in(TrBuildIn::Continue, kw) }
    pub fn add_typeof<T : Keywords>(&mut self, kw : T) -> SymbID { self._add_tr_build_in(TrBuildIn::KindOf, kw) }

    pub fn have_if(&self) -> bool { self.permission.branching_if.is_some() }
    pub fn have_loop(&self) -> bool { self.permission.looping.is_some() }
    pub fn have_break(&self) -> bool { self.permission.break_label.is_some() }
    pub fn have_continue(&self) -> bool { self.permission.continue_label.is_some() }
    pub fn have_typeof(&self) -> bool { self.permission.kind_of.is_some() }

}


/// Symbol ID to an expression stored inside the environnement
/// It is also possible to associate name and some related ExprID to the target expression, thus, making an environment
type SymbID = StableVecID<Symbol>;

impl Default for SymbID { fn default() -> Self { Self::new(___())} }

impl SymbID { fn is_root(&self) -> bool { self.value() == 0 } }
impl Display for SymbID
{
    fn fmt(&self, f: &mut Formatter<'_>) -> DResult {
       write!(f, "#{}", self.value())
    }
}

#[derive(Debug)]
pub struct Symbol
{
    _value  : Expr,
    _scope  : SymbID,
    _childs : Vec<SymbID>,
    _named   : HashMap<StringID, SymbID>,
}

impl Symbol
{
    pub fn value(&self) -> &Expr { &self._value }
    pub fn scope(&self) -> SymbID { self._scope }
}

#[derive(Default, Debug)]
pub struct Parser
{
    pub inputs : Vec<char>,
    pub idx : usize,
}

type VMParsingError = String;
impl VM
{
    pub fn parser_is_not_eof(&self) -> bool { self.parser.idx < self.parser.inputs.len() }
    pub fn parser_is_eof(&self) -> bool { !self.parser_is_not_eof() }

    pub fn parser_observe(&self) -> char { if self.parser_is_not_eof() { self.parser.inputs[self.parser.idx] } else { '\0'}}
    pub fn parser_step_back(&mut self) { self.parser.idx -= 1; }
    pub fn parser_step(&mut self) { self.parser.idx += 1; }
    pub fn parser_read(&mut self) -> char { let c = self.parser_observe(); self.parser_step(); c }

    pub fn parser_read_all(&mut self) { self.parser.idx = self.parser.inputs.len(); }

    pub fn add_compilation_unit(&mut self, code : &str) { for c in code.chars() { self.parser.inputs.push(c); } }
    
    pub fn try_add_compilation_unit_and_parse_it(&mut self, code : &str) -> Result<Expr, VMParsingError> 
    { self.add_compilation_unit(code); self.parse_next_compilation_unit() }
    pub fn add_compilation_unit_and_parse_it(&mut self, code : &str) -> Expr { self.try_add_compilation_unit_and_parse_it(code).unwrap() }

    pub fn parser_get_lexem(&self, idx_start : usize, idx_end : usize) -> String { self.parser.inputs[idx_start..idx_end].iter().collect() }


    pub fn parse_symbol(&mut self) -> Result<Expr, String> 
    {
        let idx_start = self.parser.idx;
        while (!matches!(self.parser_observe(), '(' | ')' | ' ' | '\n' | '\r' | '\t')) && self.parser_is_not_eof() { self.parser_step(); }

        let lexem = self.parser_get_lexem(idx_start, self.parser.idx);

        let n = self.string_table.add(lexem.clone());
        match self.try_bind_string_id_to_symb(n)
        {
            Some(v) => Ok(Expr::Symb(v)),
            None => Err(format!("Unknow symbol : `{}`", lexem)),
        }
        
    }

    /// strip useless spacing
    pub fn parse_useless(&mut self) { while matches!(self.parser_observe(), ' ' | '\n' | '\r' | '\t') { self.parser_read(); } }

    pub fn parse_next_compilation_unit(&mut self) -> Result<Expr, VMParsingError>
    { 
        self.parse_useless();
        if self.parser_is_eof() { return Err("".to_owned())}

        let c = self.parser_observe();
        match c
        {
            // number, or maybe a symbol
            // number : 1, 42, -8
            // symbol : -, -this-is-a-symbol-
            '0'..='9' | '-' => 
            { 
                let idx_start = self.parser.idx;
                self.parser_step();

                while matches!(self.parser_observe(), '0'..='9') { self.parser_step(); }

                if c == '-' && idx_start + 1  == self.parser.idx 
                { 
                    self.parser_step_back();
                    self.parse_symbol()
                } else { 
                    let lexem = self.parser_get_lexem(idx_start, self.parser.idx);
                    match lexem.parse::<i32>()
                    {
                        Ok(v) => Ok(Expr::I32(v)),
                        Err(e) => Err(format!("integer : {}", e)),
                    }
                }
            }
            '(' => 
            {
                self.parser_step();
                self.parse_useless();

                let mut v = vec![];
                while self.parser_observe() != ')' 
                {
                    v.push(self.parse_next_compilation_unit()?);    
                }
                self.parser_step();
                if v.is_empty() { Ok(Expr::Void) } else { self.make_callable_expr(v) }
            }
            ')' => { Err("Unexpected `)`".to_owned()) }
            _ => self.parse_symbol()
        }
    }

    fn make_callable_expr(&mut self, v : Vec<Expr>) -> Result<Expr, String>
    {
        if v.len() <= 0 { return Err("Can't call an empty func".to_owned()); }

        let t = TrCall::new(v);
        let kind = self.try_kind_of(t.tr())?;

        let Kind::Tr(tr_kind) = kind else { return Err(format!("`{}` is not callable", self.display(t.tr()))); };
        
        match *tr_kind
        {
            TrKind::BuildIn(bi) => 
            {
                let mut v : usize = 0;
                let idx = &mut v;

                match bi
                {
                    TrBuildIn::IfElse => 
                    {
                        t.check_arg(self, idx, "condition", Some(Kind::Bool))?;
                        t.check_arg(self, idx, "true value", None)?;
                        t.check_arg(self, idx, "false value", Some(t.arg_at(1).kind(self)))?;
                    },
                    TrBuildIn::Loop => todo!(),
                    TrBuildIn::Break => todo!(),
                    TrBuildIn::Continue => todo!(),
                    TrBuildIn::KindOf => 
                    {
                        t.check_arg(self, idx, "expression", None)?;
                    },
                }
                t.end_arg(self, *idx)?;
            },
            TrKind::External(tr_kind) => 
            {
                let arg_expected = tr_kind.input_kind.as_slice();
                let arg_got = t.args();
        
                let nb_arg_expected = arg_expected.len();
                let nb_arg_got = arg_got.len();
                if nb_arg_got != nb_arg_expected { return Err(format!("Expected {} arg, got {}\n> {}", nb_arg_expected, nb_arg_got, self.display(&tr_kind)))}
        
                for (idx, (expected, got)) in arg_expected.iter().zip(arg_got).enumerate()
                {
                    if !self.correct_kind(got, expected) 
                    { return Err(format!("Expected `{}` instead of `{}` for the {} arg\n> {}", self.display(expected), self.display(got), idx+1, self.display(&tr_kind)));}
                }
            }
        }
        Ok(Expr::TrCall(t))
    }

    fn correct_kind(&self, e : &Expr, expected_kind : &Kind) -> bool { &self.kind_of(e) == expected_kind }


    // Ok(Expr::TrCall(TrCall::new(v)))
}


/// ================= Print : =================

struct VMDisplay<'a, T>
{
    vm : &'a VM,
    val : T,
}
impl<'a, T> VMDisplay<'a, T>
{
    fn new(vm : &'a VM, val : T) -> Self { Self { vm, val }}
    fn display<K>(&self, val : K) -> VMDisplay<'a, K> { VMDisplay::new(self.vm, val) }
}
impl<'a, T> Deref for VMDisplay<'a, T>  { type Target=VM; fn deref(&self) -> &Self::Target { self.vm } }

impl<'a> Display for VMDisplay<'a, StringID> {
    fn fmt(&self, f: &mut Formatter<'_>) -> DResult 
    { write!(f, "`{}`", self.string_table[self.val].name()) }
}
impl<'a> Display for VMDisplay<'a, SymbID> {
    fn fmt(&self, f: &mut Formatter<'_>) -> DResult 
    { write!(f, "{}", self.val) }
}
impl<'a> Display for VMDisplay<'a, TrID> {
    fn fmt(&self, f: &mut Formatter<'_>) -> DResult 
    { write!(f, "{}", self.display(&self[self.val].kind)) }
}
impl<'a> Display for VMDisplay<'a, TrBuildIn> {
    fn fmt(&self, f: &mut Formatter<'_>) -> DResult 
    {
        match self.val
        {
            TrBuildIn::IfElse => write!(f, "If"),
            TrBuildIn::Loop => write!(f, "Loop"),
            TrBuildIn::Break => write!(f, "Break"),
            TrBuildIn::Continue => write!(f, "Continue"),
            TrBuildIn::KindOf => write!(f, "TypeOf"),
        }
    }
}
impl<'a> Display for VMDisplay<'a, &TrKind> 
{ 
    fn fmt(&self, f: &mut Formatter<'_>) -> DResult 
    {
        match self.val
        {
            TrKind::BuildIn(bi) => write!(f, "{}", self.display(*bi)),
            TrKind::External(ex) => write!(f, "{}", self.display(ex)),
        }
    }
}
impl<'a> Display for VMDisplay<'a, &TrKindExternal> 
{ 
    fn fmt(&self, f: &mut Formatter<'_>) -> DResult 
    {
        write!(f, "{}(", self.val.cat)?;

        let mut it = self.val.input_kind.iter().peekable();
        while let Some(arg) = it.next()
        {
            write!(f, "{}", self.display(arg))?;
            if it.is_not_last() { write!(f, ", ")?; }
        }
        write!(f, ")")?;
        if !self.val.output.is_void() { write!(f, " -> {}", self.display(&self.val.output))?; }
        Ok(())
    }
}
impl<'a> Display for VMDisplay<'a, &Kind> {
    fn fmt(&self, f: &mut Formatter<'_>) -> DResult 
    { 
        match self.val
        {
            Kind::Void => write!(f, "()"),
            Kind::I32 => write!(f, "i32"),
            Kind::Bool => write!(f, "bool"),
            Kind::Kind => write!(f, "Type"),
            Kind::Any => write!(f, "any"),
            Kind::Tr(tr) => write!(f, "{}", self.display(&**tr)),
        }
    }
}
impl<'a> Display for VMDisplay<'a, &TrCall> {
    fn fmt(&self, f: &mut Formatter<'_>) -> DResult 
    {
        write!(f, "(")?;
        let mut it = self.val.iter().peekable();
        while let Some(v) = it.next()
        {
            write!(f, "{}", self.display(v))?;
            if it.is_not_last() { write!(f, " ")?; }
        }
        write!(f, ")")
    }
}
impl<'a> Display for VMDisplay<'a, &Expr> {
    fn fmt(&self, f: &mut Formatter<'_>) -> DResult 
    {
        match self.val
        {
            Expr::Void => write!(f, "()"),
            Expr::I32(v) => write!(f, "{}", v),
            Expr::Bool(v) => write!(f, "{}", v),
            Expr::Kind(v) => write!(f, "{}", self.display(v)),

            //Expr::UncompiledSymb(v) => self.print_string_id(*v),
            Expr::Symb(s) => write!(f, "{}", s),
            Expr::Tr(tr) => write!(f, "{}", self.display(*tr)),
            Expr::TrCall(v) => write!(f, "{}", self.display(v)),

            Expr::Break(_, _) => panic!("Break can't be eval"),
            Expr::Continue(_) => panic!("Continue can't be eval"),
        }
    }
}


impl VM
{
    pub fn print(&self) 
    {
        self.print_string_table();
        println!();

        self.print_fn_table();
        println!();

        self.print_env();
        println!();
    }
    
    pub fn print_string_table(&self) 
    {
        println!("string table :");
        for (idx, e) in self.string_table.iter_with_value()
        {
            println!("{:2} | {}", idx, e);
        }
    }

    pub fn print_fn_table(&self) 
    {
        println!("fn table :");
        for idx in 0..self.tr_table.len()
        {
            println!("{:2} | {:?}", idx, TrID::new(idx));
        }
    }

    pub fn print_string_id(&self, v : StringID) { print!("{}", self.display(v)) }
    pub fn print_symb_id(&self, v : SymbID) { print!("{}", self.display(v)) }
    pub fn print_fn(&self, v : TrID) { print!("{}", self.display(v)) }
    pub fn print_kind(&self, v : &Kind) { print!("{}", self.display(v)) }
    pub fn print_expr(&self, v : &Expr) { print!("{}", self.display(v)) }

    fn display<K>(&self, val : K) -> VMDisplay<K> { VMDisplay::new(self, val) }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Padding {
    Blank,
    Bar
}

impl VM
{
    pub fn print_env(&self) 
    {
        println!("env :");
        self._print_ev(___(), &mut vec![], false, &mut String::new());
    }

    fn print_named(&self, h : &HashMap<StringID, SymbID>)
    {
        if h.is_empty() { return; }
        let mut it = h.iter().peekable();
        print!("{{");
        while let Some((k, v)) = it.next()
        {
            self.print_string_id(*k);
            print!(" => ");
            self.print_symb_id(*v);
            if it.is_not_last() { print!(", "); }
        }
        print!("}}");
    }

    /// Thank to https://cronokirby.com/posts/2020/12/a-unix-tree-algorithm/
    fn _print_ev(&self, id : SymbID, prev: &mut Vec<Padding>, last: bool, s : &mut String) 
    {
        s.clear();
        if !prev.is_empty() 
        {
            for p in prev.iter().take(prev.len() - 1)
            {
                match p
                {
                    Padding::Blank => s.push_str("    "),
                    Padding::Bar => s.push_str("|   "),
                }
            }
            if last {
                s.push_str("\\=> ");
            } else {
                s.push_str("|=> ");
            }
        }

        let frame = &self.env[id];
        s.push_str(&format!("{} : {}", self.display(id), self.display(frame.value())));

        print!("{: <32}  ", s);
        //print!("{: <5}  ", format!("{} use", frame.nb_use()));
        self.print_named(&frame._named);
        println!();
        
        if !frame._childs.is_empty()
        {
            let mut it = frame._childs.iter().peekable();
            while let Some(child) = it.next().copied()
            {
                let is_last = it.is_last();
                prev.push(if is_last { Padding::Blank } else { Padding::Bar });

                self._print_ev(child, prev, is_last, s);
                prev.pop();
            }
        }
    }
}


impl VM
{
    pub fn test_eval_repl(&mut self, code : &str)
    {
        self.add_compilation_unit(code);

        while !self.parser_is_eof()
        {
            match self.parse_next_compilation_unit()
            {
                Ok(expr) => 
                {
                    print!("=> ");
                    let e = self.eval(expr);
                    self.print_expr(&e);
                    println!();
                },
                Err(err) => 
                {
                    self.parser_read_all();
                    println!("{}", err);
                    if !err.is_empty() { println!(); }
                    return;
                },
            }
        }
    }

    pub fn test_eval(&mut self, code : &str)
    {
        println!("{}", code);
        match self.try_add_compilation_unit_and_parse_it(code)
        {
            Ok(expr) => 
            {
                println!("parse => {:?}", expr);
          
                print!("eval  => ");
                let e = self.eval(expr);
                self.print_expr(&e);
                println!();
            },
            Err(err) => 
            {
                println!("{}", err);
            },
        }
        println!();
    }
}