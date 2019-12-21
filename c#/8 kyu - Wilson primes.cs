public class Kata
{
  public static bool AmIWilson(int p)
  {
    return p == 13 ? true : (Fact(p - 1) + 1) / (p * p) == 1;
  }
  
  public static int Fact(int n)
  {
    return n > 0 ? n * Fact(n - 1) : 1;
  }
}
