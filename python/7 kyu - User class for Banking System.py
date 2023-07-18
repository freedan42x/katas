class User(object):
    def __init__(self, name, balance, checking_account):
        self.name = name
        self.balance = balance
        self.checking_account = checking_account
    
    def withdraw(self, money):
        if money > self.balance:
            raise ValueError('not enough money to withdraw')
        self.balance -= money
        return f'{self.name} has {self.balance}.'
    
    def check(self, other, money):
        if money > other.balance:
            raise ValueError('not enough money to check')
        if not other.checking_account:
            raise ValueError('not checking account')
        self.balance += money
        other.balance -= money
        return f'{self.name} has {self.balance} and {other.name} has {other.balance}.'
    
    def add_cash(self, money):
        self.balance += money
        return f'{self.name} has {self.balance}.'
