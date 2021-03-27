use std::fmt;

pub struct Paren<T>(pub usize, pub usize, pub T);

impl<T: fmt::Display> fmt::Display for Paren<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.0 <= self.1 {
            write!(f, "({})", self.2)
        } else {
            write!(f, "{}", self.2)
        }
    }
}
