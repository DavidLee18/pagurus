void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void cf(int c,void*p){if(c)free(p);}
int main(void){int*p=malloc(4);cf(0,p);free(p);return 0;}
