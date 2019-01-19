public class Multiplier
{
  public static int Multiply(int x) =>
    x * (x % 2 == 0 ? 8 : 9);
}  
