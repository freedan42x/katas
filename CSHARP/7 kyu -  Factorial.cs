using System;

namespace Solution
{
  public static class Program
  {
    public static int factorial(int n)
      => n > 1 ? n * factorial(--n) : 1;
  }
}
