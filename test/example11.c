#include "verifier.h"

int main() {
  int x = input();
  int y = input();
  assume(x > 1);
  assume(y >= 3);
  if (x > 3) {
    x = x + 7;
  } else {
    x = 11;
  }
  assert(x + y > 13);
  return 0;
}
