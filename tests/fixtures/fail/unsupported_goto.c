/* FAIL: goto is rejected rather than modelled unsoundly. */
int main(void) {
    goto skip;
skip:
    return 0;
}
