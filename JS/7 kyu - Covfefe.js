const covfefe = str => /coverage/.test(str) === true ? str.replace(/coverage/g, 'covfefe') : str += ' covfefe';
