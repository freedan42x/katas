const validISBN10=isbn=> {
    if(!/[0-9]{9}[0-9X]/.test(isbn))
      return false;
    isbn = isbn.split("").map((a,i) => ((a==="X") ? 10 : a) *(i+1));
    return isbn.reduce((x,y)=>x+y) % 11 === 0;
}
