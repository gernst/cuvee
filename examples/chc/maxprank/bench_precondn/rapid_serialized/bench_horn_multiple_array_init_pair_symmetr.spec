func main()
{
        Int[] a;
	Int[] b;
	Int[] c;
        const Int alength;
        Int i = 1;

        while(i < alength)
        {
	  const Int x;
	  a[i] = x;
	  b[i] = (0-1)*x;
	  i = i + 1;
        }
        i = 0;
        while (i < alength)
        {
          c[i] = a[i] + b[i];
          i = i + 1;
        }
}

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (< 0 pos)
          (< pos alength)
          (<= alength (i main_end))
         )
       (= 0 (c main_end pos))
      )
   )
)
