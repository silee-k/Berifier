#include "verifier.h"

int main() {
  int x = input();
  while (0 < x) {
    x++;
  }
  assert(x == 0);
  return 0;
}
