const defineSuit = card => card[card.length-1] === '♣' ? 'clubs' : card[card.length-1] === '♠' 
                                                       ? 'spades' : card[card.length-1] === '♦' 
                                                       ?'diamonds' : 'hearts';
