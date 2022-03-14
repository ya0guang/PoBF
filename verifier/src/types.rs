pub struct A(u32);

impl A {
    pub fn new(x: u32) -> Self {
        A(x)
    }

    pub fn to_b(&self) -> B {
        B(self.0)
    }
}

pub struct B(u32);

