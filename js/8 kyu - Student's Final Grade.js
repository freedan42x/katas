const finalGrade = (g, p) => g > 90 || p > 10 ? 100 : g > 75 && p >= 5 ? 90 : g > 50 && p >= 2 ? 75 : 0;
