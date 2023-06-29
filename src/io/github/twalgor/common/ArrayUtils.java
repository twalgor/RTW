package io.github.twalgor.common;

public class ArrayUtils {
  public static Integer[] box(int[] a) {
    Integer[] b = new Integer[a.length];
    for (int i = 0; i < a.length; i++) {
      b[i] = a[i];
    }
    return b;
  }

  public static int[] unbox(Integer[] a) {
    int[] b = new int[a.length];
    for (int i = 0; i < a.length; i++) {
      b[i] = a[i];
    }
    return b;
  }
}
