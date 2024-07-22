func main()
{
        Int[] a;
	Int[] b;
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
	  Int tmp= a[i];
	  a[i] = (0-1)* b[i];
	  b[i] = tmp;
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
       (not (= (a main_end pos) (b main_end pos)))
      )
   )
)
