/* FAIL: a non-consuming wrapper that returns malloc is Ghost, not Null.
   Treating that as known-null would hide this double free. */
void *malloc(unsigned long n);
void free(void *p);
void *wrap(void) { return malloc(4); }
int main(void) {
    void *p = wrap();
    free(p);
    free(p);
    return 0;
}
