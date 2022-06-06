#include "verifier.h"

int main() {
  int x = input();
  while (x == x) {
    x++;
  }
  assert(x != x);
  return 0;
}
