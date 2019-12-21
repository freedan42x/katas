function searchSubstr(fullText, searchText, allowOverlap=true) {
    if (searchText==''||fullText=='') 
      return 0;
    
    var 
      re   = new RegExp(searchText, 'g'),
      _re  = new RegExp(searchText[0], 'g'),
      a    = fullText.match(re).length,
      _a   = fullText.match(_re).length;
      
     if (!allowOverlap || a === _a/searchText.length)
       return a;

     return ~~(_a/searchText.length)+1;
}
