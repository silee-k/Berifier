#include "verifier.h"

int main() {
  int x = input();
  int y = input();
  assume(y > 0);
  if (x >= 0) {
    x = x * y;
  } else {
    x = -x;
  }
  assert(x > 0);
  return 0;
}
