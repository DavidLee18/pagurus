/* PASS: two frees of a known-null pointer are both no-ops. */
void free(void *p);

int main(void) {
    void *p = 0;
    free(p);
    free(p);
    return 0;
}
