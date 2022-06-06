#include "verifier.h"

int main() {
  int m = input();
  int n = input();
  int r;
  assume(m > 0);
  assume(n > 0);
  while (n > 0) {
    while (m - n >= 0) {
      m = m - n;
    }
    r = m;
    m = n;
    n = r;
  }
  assert(n == 0 || m == 0);
}
