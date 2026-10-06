/* FAIL: maybe-consumed must not be used afterwards, even if this path
   does not take the free. */
void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void cf(int c,void*p){if(c)free(p);}
int main(void){int*p=malloc(4);cf(0,p);*p=1;free(p);return 0;}
