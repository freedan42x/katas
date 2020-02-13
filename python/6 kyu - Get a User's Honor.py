from urllib.request import urlopen
from bs4 import BeautifulSoup

def get_honor(username):
  source = urlopen(f'https://www.codewars.com/users/{username}')
  soup = BeautifulSoup(source, 'html.parser')
  
  return int(
    soup
    .body
    .find(id='app')
    .find(id='shell')
    .find(id='shell_content')
    .find(class_='pam')
    .find(class_='row')
    .div.section.find_all(class_='stat')[1]
    .text[6:]
    .replace(',', '')
  )
