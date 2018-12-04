object test {
  def test(): Unit = {()}
  val l: L.List = L.Cons(5, L.Cons(-5, L.Cons(-1, L.Cons(0, L.Cons(10, L.Nil())))));
  true == ()
}