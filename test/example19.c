#include "verifier.h"

int main() {
  int m = 42;
  int n = 20;
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
  assert(m == 0 || n == 0);
}
