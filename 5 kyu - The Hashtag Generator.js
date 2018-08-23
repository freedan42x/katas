const generateHashtag=s=>{
  var str = '#'+s.trim().replace(/\b\w/g,e=>e.toUpperCase()).replace(/\s/g,'');
  return (str.length>140||str=='#')?false:str;
}
