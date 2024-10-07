#![allow(unused_imports)]
#![allow(unused_variables)]
//#![allow(dead_code)]

use std::{collections::HashMap, fmt::{Debug, Display, Formatter, Result as DResult}, io::BufRead, marker::PhantomData, ops::{Index, *}, rc::Rc};
pub use default_is_triple_underscore::*;

pub mod extension;
pub use extension::*;

pub mod string_table;
pub use string_table::*;

pub mod stable_vec;
pub use stable_vec::*;

pub mod vm;
pub use vm::*;


impl VM
{
    pub fn add_standard_lib(&mut self)
    {
        self.add("zero", 0i32);

        self.add("true", true);
        //self.add("vrai", true);
        self.add("false", false);

        self.add("void", ());
        self.add("bool", Kind::Bool);
        self.add("i32", Kind::I32);
        self.add("type", Kind::Kind);

        self.add("+", |x: i32, y: i32| x + y);
        self.add("-", |x: i32, y: i32| x - y);
        self.add("*", |x: i32, y: i32| x * y);
        self.add("/", |x: i32, y: i32| x / y);
    
        self.add(">", |x: i32, y: i32| x > y);
        self.add(">=", |x: i32, y: i32| x >= y);
        self.add("<", |x: i32, y: i32| x < y);
        self.add("<=", |x: i32, y: i32| x <= y);
        self.add("==", |x: i32, y: i32| x == y);
        self.add("!=", |x: i32, y: i32| x != y);
    
        self.add("&", |x: bool, y: bool| x & y);
        self.add("|", |x: bool, y: bool| x | y);

        self.add("!", |x: bool| !x);


        self.add("print", |x: Expr| { println!("printing {:?}", x); });

        self.add_if("if");
        self.add_loop(vec!["loop", "forever"]);
        self.add_break("break");
        self.add_continue("continue");
        self.add_typeof("typeof");
    }
}

pub fn repl(vm : &mut VM)
{
    loop
    {
        let mut ln = String::new();
        std::io::stdin().lock().read_line(&mut ln).expect("can't read the line");
        vm.test_eval_repl(&ln);
    }
}
pub fn main()
{
    for i in 0..10 { println!(); }

    let mut vm = VM::new();
    vm.add_standard_lib();

    vm.print_env();
    println!();

    //vm.test_eval("(- 10 2)");
    //vm.test_eval("((if (== 2 (+ 1 1)) + -) 10 20)");
    vm.test_eval("(== 1 2)");
    vm.test_eval("(== 1 (- 2 1))");

    vm.test_eval("(& true false)");


    vm.test_eval("(if true 100 200)");

    vm.test_eval("((if true + -) 100 50)");



    //println!();
    //vm.test_eval("(& true false)");
    //vm.test_eval("(if false 1 0)");
    //vm.test_eval("(loop (print 42))");
    //vm.test_eval("()");
    //vm.test_eval("void");
    //vm.test_eval("(loop (break 0 ()))");
    //vm.test_eval("(loop (loop (break 1 42)))");
    //vm.test_eval("(loop (loop (break 1 42)))");
    //vm.test_eval("(typeof true)");
    //vm.test_eval("i32");
    //vm.test_eval("(name x 42)");
    //vm.test_eval("(+ 1 true)");
    //vm.test_eval("(+ 1 (+ 2 3))");
    //vm.test_eval("(typeof forever)");
    //vm.test_eval("(typeof (loop (break 1)))");
    //vm.test_eval("(+ 1 2)");

    repl(&mut vm);

    println!();
    println!("done");
}

/*
stmt
variable
type checking
bytecode/opti
user fn call
structure/union
step by step
never type / panics
traits


variable : must be named ?


=== declaration ===
let x : i32;


(lambda::let i32)

(named x 
    (lambda::let i32)
)


*/