#include "verifier.h"

int main() {
  int x = input();
  while (x == 0) {
    x++;
  }
  assert(x != 0);
  return 0;
}
