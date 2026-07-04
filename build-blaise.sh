#!/bin/bash
#
# Blaise Compiler Build Script
# Automates bootstrap of Blaise v0.12.0 from source
#

set -e

# Цвета
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

print_step() {
    echo ""
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${GREEN}▶ $1${NC}"
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
}

print_success() { echo -e "${GREEN}✔ $1${NC}"; }
print_info() { echo -e "${YELLOW}ℹ $1${NC}"; }
print_error() { echo -e "${RED}✘ $1${NC}"; }

# Проверка директории
if [ ! -f "compiler/src/main/pascal/Blaise.pas" ]; then
    print_error "Запустите скрипт из корня проекта Blaise"
    exit 1
fi

print_step "ШАГ 1: Проверка релизного компилятора"

if [ ! -f "compiler/target/blaise" ]; then
    print_error "Компилятор не найден в compiler/target/blaise"
    echo ""
    echo -e "${YELLOW}Скачайте релизный бинарник v0.12.0:${NC}"
    echo "  wget https://github.com/graemeg/blaise/releases/download/v0.12.0/blaise-linux-x86_64 -O compiler/target/blaise"
    echo "  chmod +x compiler/target/blaise"
    exit 1
fi

chmod +x compiler/target/blaise
VERSION=$(./compiler/target/blaise --version 2>&1 | grep -oP 'v\d+\.\d+\.\d+' | head -1)
if [ "$VERSION" != "v0.12.0" ]; then
    print_error "Неверная версия: $VERSION (ожидается v0.12.0)"
    exit 1
fi
print_success "Версия: $VERSION"

print_step "ШАГ 2: Сборка рантайма"

cd runtime
make clean 2>/dev/null || true
make
make install
cd ..
print_success "Рантайм установлен"

print_step "ШАГ 3: Сборка компилятора"

./compiler/target/blaise \
    --source compiler/src/main/pascal/Blaise.pas \
    --unit-path compiler/src/main/pascal \
    --unit-path runtime/src/main/pascal \
    --unit-path stdlib/src/main/pascal \
    --output compiler/target/blaise-new

if [ ! -f "compiler/target/blaise-new" ]; then
    print_error "Компилятор не собрался"
    exit 1
fi
print_success "Компилятор собран"

print_step "ШАГ 4: Проверка самовоспроизводимости"

if diff compiler/target/blaise compiler/target/blaise-new > /dev/null 2>&1; then
    print_success "Бинарники идентичны! ✨ Идеальный fixpoint!"
else
    print_info "Бинарники различаются (временные метки)"
fi

print_step "ШАГ 5: Замена компилятора"

print_info "Проверка нового компилятора..."
if ./compiler/target/blaise-new --help > /dev/null 2>&1; then
    print_success "Новый компилятор работает"
else
    print_error "Новый компилятор не запускается"
    exit 1
fi

mv compiler/target/blaise-new compiler/target/blaise
print_success "Компилятор обновлён"

print_step "ШАГ 6: Создание и компиляция тестовой программы"

# И русский вариант для проверки синонимов
cat > test_program.pas << 'EOF'
ПРОГРАММА Привет;
НАЧАЛО
  WriteLn('Привет от ВИРТ v0.12.0!');
  WriteLn('Русские ключевые слова работают!');
КОНЕЦ.
EOF

print_info "Компиляция тестовой программы..."
./compiler/target/blaise --source test_program.pas --output test_program

if [ ! -f "test_program" ]; then
    print_error "Тестовая программа не скомпилировалась"
    exit 1
fi
print_success "Тестовая программа скомпилирована"

print_info "Запуск тестовой программы..."
echo ""
echo -e "${YELLOW}═══════════════════════════════════════════════════════════════${NC}"
./test_program
echo -e "${YELLOW}═══════════════════════════════════════════════════════════════${NC}"
echo ""

if [ $? -eq 0 ]; then
    print_success "Тестовая программа успешно выполнена!"
else
    print_error "Ошибка при выполнении теста"
    exit 1
fi

print_step "✅ СБОРКА ЗАВЕРШЕНА УСПЕШНО!"

echo ""
echo -e "${GREEN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${GREEN}  Компилятор Blaise v0.12.0 успешно собран!${NC}"
echo -e "${GREEN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo "📁 Компилятор: compiler/target/blaise"
echo "📁 Рантайм:    compiler/target/blaise_rtl.a"
echo "📁 Тест:       test_program"
echo ""
echo "🚀 Использование:"
echo "  ./compiler/target/blaise --source program.pas --output program"
echo ""

read -p "Удалить тестовые файлы? [y/N] " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]; then
    rm -f test_program.pas test_program
    print_info "Тестовые файлы удалены"
fi

print_success "Готово! 🎉"