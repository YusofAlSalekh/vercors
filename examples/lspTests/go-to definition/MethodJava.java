class GoToDefTest {

  /*@
    ensures \result == (x >= y ? x : y);
  @*/
  public int max(int x, int y) {
    return (x >= y) ? x : y;
  }

  /*@
    ensures \result == (x <= y ? x : y);
  @*/
  public int min(int x, int y) {
    return (x <= y) ? x : y;
  }

  int a, b;

  /*@
    requires a >= 0 && b >= 0;
    ensures a == \old(a);
    ensures b == \old(b);
    ensures \result == max(a, b);
  @*/
  public int computeMax() {
    return max(a, b);
  }

  /*@
    requires a >= 0 && b >= 0;
    ensures \result == min(a, b);
  @*/
  public int computeMin() {
    return min(a, b);
  }
}
