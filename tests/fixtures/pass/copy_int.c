/* Integers are copy types: assignment does not invalidate the source. */
int main(void) {
    int a = 1;
    int b = a;
    int c = a + b;
    return c;
}
