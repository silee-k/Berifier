#include "verifier.h"
int main(void) {
  int n, k, j;
  n = input();
  k = input();
  assume(k >= 2);
  assume(n < 1);
  j = 0;
  while (j < n) {
    j++;
    k--;
  }
  assert(k >= 0);
  return 0;
}
