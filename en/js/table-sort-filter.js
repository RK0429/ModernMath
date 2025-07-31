/**
 * Table Sort and Filter functionality for Article Progress tables
 */
(function () {
  "use strict";

  // Wait for DOM to be ready
  document.addEventListener("DOMContentLoaded", function () {
    initializeProgressTables();
  });

  function initializeProgressTables() {
    // Find all progress tables
    const tables = document.querySelectorAll(".progress-table");

    tables.forEach((table) => {
      // Add sorting functionality
      addSortingToTable(table);

      // Add filtering functionality
      addFilteringToTable(table);
    });
  }

  /**
   * Add sorting functionality to table headers
   */
  function addSortingToTable(table) {
    const headers = table.querySelectorAll("thead th");

    headers.forEach((header, index) => {
      // Skip the last column (formal proof) for sorting
      if (index < headers.length - 1) {
        header.classList.add("sortable");

        // Add sort indicator
        const sortIndicator = document.createElement("span");
        sortIndicator.className = "sort-indicator";
        sortIndicator.innerHTML = "⇅";
        header.appendChild(sortIndicator);

        // Add click event
        header.addEventListener("click", function () {
          sortTable(table, index, header);
        });
      }
    });
  }

  /**
   * Sort table by column
   */
  function sortTable(table, columnIndex, header) {
    const tbody = table.querySelector("tbody");
    const rows = Array.from(tbody.querySelectorAll("tr"));
    const sortIndicator = header.querySelector(".sort-indicator");

    // Determine sort direction
    const currentDirection = header.getAttribute("data-sort") || "none";
    let newDirection;

    if (currentDirection === "none" || currentDirection === "desc") {
      newDirection = "asc";
      sortIndicator.innerHTML = "↑";
    } else {
      newDirection = "desc";
      sortIndicator.innerHTML = "↓";
    }

    // Reset other headers
    table.querySelectorAll("thead th").forEach((th) => {
      if (th !== header) {
        th.setAttribute("data-sort", "none");
        const ind = th.querySelector(".sort-indicator");
        if (ind) ind.innerHTML = "⇅";
      }
    });

    header.setAttribute("data-sort", newDirection);

    // Sort rows
    rows.sort((a, b) => {
      const aCell = a.cells[columnIndex];
      const bCell = b.cells[columnIndex];

      // Extract text content, removing HTML tags
      const aText = aCell.textContent.trim();
      const bText = bCell.textContent.trim();

      // Natural sort comparison
      const comparison = aText.localeCompare(bText, undefined, {
        numeric: true,
      });

      return newDirection === "asc" ? comparison : -comparison;
    });

    // Re-append sorted rows
    rows.forEach((row) => tbody.appendChild(row));
  }

  /**
   * Add filtering functionality to table
   */
  function addFilteringToTable(table) {
    const thead = table.querySelector("thead");
    const filterRow = document.createElement("tr");
    filterRow.className = "filter-row";

    const headers = thead.querySelectorAll("th");
    const filters = [];

    // Detect language once for all filters
    const isJapanese =
      document.documentElement.lang === "ja" ||
      window.location.pathname.includes("/ja/");

    headers.forEach((header, index) => {
      const filterCell = document.createElement("th");

      if (index === 1) {
        // Type column - add dropdown
        const select = document.createElement("select");
        select.className = "filter-select";

        // Add options
        if (isJapanese) {
          select.innerHTML = `
            <option value="">すべてのタイプ</option>
            <option value="定義">定義</option>
            <option value="定理">定理</option>
            <option value="公理">公理</option>
            <option value="例">例</option>
            <option value="命題">命題</option>
            <option value="補題">補題</option>
            <option value="系">系</option>
          `;
        } else {
          select.innerHTML = `
            <option value="">All Types</option>
            <option value="Definition">Definition</option>
            <option value="Theorem">Theorem</option>
            <option value="Axiom">Axiom</option>
            <option value="Example">Example</option>
            <option value="Proposition">Proposition</option>
            <option value="Lemma">Lemma</option>
            <option value="Corollary">Corollary</option>
          `;
        }

        filterCell.appendChild(select);
        filters.push({ element: select, index: index, type: "select" });
      } else if (index === 2) {
        // Status column - add dropdown
        const select = document.createElement("select");
        select.className = "filter-select";

        // Add options
        if (isJapanese) {
          select.innerHTML = `
            <option value="">すべてのステータス</option>
            <option value="完成">完成</option>
            <option value="草稿">草稿</option>
            <option value="スタブ">スタブ</option>
          `;
        } else {
          select.innerHTML = `
            <option value="">All Status</option>
            <option value="complete">Complete</option>
            <option value="draft">Draft</option>
            <option value="stub">Stub</option>
          `;
        }

        filterCell.appendChild(select);
        filters.push({ element: select, index: index, type: "select" });
      } else if (index === 3) {
        // Proof status column - add dropdown
        const select = document.createElement("select");
        select.className = "filter-select";

        // Add options
        if (isJapanese) {
          select.innerHTML = `
            <option value="">すべての証明</option>
            <option value="✅">完成</option>
            <option value="⚠️">警告あり</option>
            <option value="❌">エラーあり</option>
            <option value="📝">未実装</option>
          `;
        } else {
          select.innerHTML = `
            <option value="">All Proofs</option>
            <option value="✅">Completed</option>
            <option value="⚠️">Warnings</option>
            <option value="❌">Errors</option>
            <option value="📝">Not implemented</option>
          `;
        }

        filterCell.appendChild(select);
        filters.push({ element: select, index: index, type: "select" });
      } else if (index === 0) {
        // Concept column - add text input
        const input = document.createElement("input");
        input.type = "text";
        input.className = "filter-input";
        input.placeholder = isJapanese ? "フィルター..." : "Filter...";

        filterCell.appendChild(input);
        filters.push({ element: input, index: index, type: "text" });
      }

      filterRow.appendChild(filterCell);
    });

    // Insert filter row after headers
    thead.appendChild(filterRow);

    // Add filter event listeners
    filters.forEach((filter) => {
      const eventType = filter.type === "select" ? "change" : "input";
      filter.element.addEventListener(eventType, function () {
        filterTable(table, filters);
      });
    });

    // Add clear filters button
    addClearFiltersButton(table, filters);
  }

  /**
   * Filter table based on active filters
   */
  function filterTable(table, filters) {
    const tbody = table.querySelector("tbody");
    const rows = tbody.querySelectorAll("tr");
    let visibleCount = 0;

    rows.forEach((row) => {
      let shouldShow = true;

      filters.forEach((filter) => {
        const filterValue = filter.element.value.toLowerCase();
        if (filterValue) {
          const cellText = row.cells[filter.index].textContent.toLowerCase();

          if (filter.type === "text") {
            // Text filter - partial match
            if (!cellText.includes(filterValue)) {
              shouldShow = false;
            }
          } else {
            // Select filter - check for value or emoji match
            if (!cellText.includes(filterValue)) {
              shouldShow = false;
            }
          }
        }
      });

      row.style.display = shouldShow ? "" : "none";
      if (shouldShow) visibleCount++;
    });

    // Update result count
    updateFilterResultCount(table, visibleCount, rows.length);
  }

  /**
   * Add clear filters button
   */
  function addClearFiltersButton(table, filters) {
    const container = table.parentElement;

    const clearButton = document.createElement("button");
    // Detect language
    const isJapanese =
      document.documentElement.lang === "ja" ||
      window.location.pathname.includes("/ja/");

    clearButton.textContent = isJapanese
      ? "すべてのフィルターをクリア"
      : "Clear All Filters";
    clearButton.className = "clear-filters-btn";
    // Style is now handled by CSS class

    clearButton.addEventListener("click", function () {
      filters.forEach((filter) => {
        filter.element.value = "";
      });
      filterTable(table, filters);
    });

    container.insertBefore(clearButton, table);
  }

  /**
   * Update filter result count display
   */
  function updateFilterResultCount(table, visible, total) {
    let countDisplay = table.parentElement.querySelector(".filter-count");

    if (!countDisplay) {
      countDisplay = document.createElement("div");
      countDisplay.className = "filter-count";
      table.parentElement.insertBefore(countDisplay, table);
    }

    if (visible === total) {
      countDisplay.style.display = "none";
    } else {
      countDisplay.style.display = "block";
      // Detect language
      const isJapanese =
        document.documentElement.lang === "ja" ||
        window.location.pathname.includes("/ja/");

      countDisplay.textContent = isJapanese
        ? `${total}件中${visible}件を表示`
        : `Showing ${visible} of ${total} entries`;
    }
  }
})();
