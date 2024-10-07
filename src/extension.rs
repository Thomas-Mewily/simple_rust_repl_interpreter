// Thank to @ctrl-alt-delor on `https://stackoverflow.com/questions/67872308/how-to-check-if-for-loop-is-on-the-last-element-of-an-iterator`
pub trait IterEndPeek 
{ 
    fn is_last(&mut self) -> bool;
    fn is_not_last(&mut self) -> bool { !self.is_last() }
}
impl<I: Iterator> IterEndPeek for  std::iter::Peekable<I> 
{
    fn is_last(&mut self) -> bool { self.peek().is_none() }
}